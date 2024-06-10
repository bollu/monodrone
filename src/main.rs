#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")] // hide console window on Windows in release
#![allow(rustdoc::missing_crate_level_docs)] // it's an example

use std::borrow::BorrowMut;
use std::process::Output;
use std::sync::Mutex;
use std::{fs::File, sync::Arc};

use midi::Message::Start;
use monodroneffi::Note;
use raylib::prelude::*;
use tinyaudio::{run_output_device, OutputDeviceParameters};
use tinyaudio::prelude::*;

const GOLDEN_RATIO: f32 = 1.61803398875;

use rustysynth::{MidiFile, MidiFileSequencer, SoundFont, Synthesizer, SynthesizerSettings};
use tracing_subscriber::layer::SubscriberExt;
use tracing::{event, Level};
mod monodroneffi;
mod leanffi;

use std::cmp;

// TODO: read midi 

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NoteEvent {
    NoteOn { pitch : u8, instant : u64 },  
    NoteOff { pitch : u8, instant : u64 },  
} 

impl NoteEvent {
    fn instant(&self) -> u64 {
        match self {
            NoteEvent::NoteOn { instant, .. } => *instant,
            NoteEvent::NoteOff { instant, .. } => *instant,
        }
    }

    fn pitch(&self) -> u8 {
        match self {
            NoteEvent::NoteOn { pitch, .. } => *pitch,
            NoteEvent::NoteOff { pitch, .. } => *pitch,
        }
    }
        
}

// order note events by instant
impl PartialOrd for NoteEvent {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        // compare tuple of (instant, pitch)
        Some((self.instant(), self.pitch()).cmp(&(other.instant(), other.pitch())))
    }
}

impl Ord for NoteEvent {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // compare tuple of (instant, pitch)
        (self.instant(), self.pitch()).cmp(&(other.instant(), other.pitch()))
    }
}

/// Get the note events at a given time instant.
fn track_get_note_events_at_time (track : &monodroneffi::Track, instant : u64) -> Vec<NoteEvent> {
    let mut note_events = Vec::new();
    for note in track.notes.iter() {
        if note.start == instant {
            note_events.push(NoteEvent::NoteOn { pitch : note.pitch as u8, instant });
        }
        if note.start + note.nsteps + 1 == instant {
            note_events.push(NoteEvent::NoteOff { pitch : note.pitch as u8, instant });
        }
    }
    note_events
}

pub struct MidiSequencer {
    synthesizer: Synthesizer,
    track : monodroneffi::Track,
    playing : bool,
    // start_instant : u64, // instant of time we started playing.
    // end_instant : u64, 
    cur_instant : u64, // current instant of time, as we last heard.
    last_rendered_instant : u64, // instant of time we last rendered.
    // looping : bool,
}

impl MidiSequencer {
    /// Initializes a new instance of the sequencer.
    ///
    /// # Arguments
    ///
    /// * `synthesizer` - The synthesizer to be handled by the sequencer.
    /// * `track` - The track to be played for this sequencer.
    pub fn new(synthesizer: Synthesizer) -> Self {
        Self {
            synthesizer,
            track : monodroneffi::Track::new(),
            playing: false,
            cur_instant: 0,
            last_rendered_instant: 0,
            // looping : false,
            // start_instant : 0,
            // end_instant : 0
        }
    }

    pub fn set_track(&mut self, track : monodroneffi::Track) {
        assert! (!self.playing); // we cannot change the track while playing.
        self.track = track;
    }

    pub fn toggle_is_playing(&mut self) {
        self.playing = !self.playing;
    }

    /// Stops playing. Keep current location.
    pub fn stop(&mut self) {
        self.synthesizer.reset();
        self.playing = false;
    }

    fn process_and_render(&mut self, left: &mut [f32], right: &mut [f32]) {
        let new_instant = self.cur_instant + 1; 
        event!(Level::INFO, "process_and_render cur({}) -> new({}) | last rendered({}) | is_playing({})", 
        self.cur_instant, new_instant, self.last_rendered_instant, self.playing);

        if (!self.playing) {
            left.fill(0f32);
            right.fill(0f32);
            event!(Level::INFO, "-> done [!playing]");
            return;
        }

        assert!(self.last_rendered_instant <= self.cur_instant);
        assert!(self.cur_instant <= new_instant);
        self.cur_instant = new_instant;
        
        assert!(left.len() == right.len());
        assert!(left.len() >= self.synthesizer.get_block_size()); // we have enough space to render at least one block.

        let mut nwritten : usize = 0;
        while(self.last_rendered_instant < new_instant && 
            // we have space enough for another block.
            self.synthesizer.get_block_size() + nwritten < left.len()) {

            let note_events = track_get_note_events_at_time(&self.track, self.last_rendered_instant);
            for note_event in note_events.iter() {
                event!(Level::INFO, "note_event: {:?}", note_event);
                match note_event {
                    NoteEvent::NoteOn { pitch, .. } => {
                        self.synthesizer.note_on(0, *pitch as i32, 100);
                    },
                    NoteEvent::NoteOff { pitch, .. } => {
                        self.synthesizer.note_off(0, *pitch as i32);
                    },
                }
            }
            assert!(self.synthesizer.get_block_size() + nwritten < left.len());
            // synthesizer writes in block_size.
            self.synthesizer.render(&mut left[nwritten..], &mut right[nwritten..]);
            nwritten += self.synthesizer.get_block_size();
            self.last_rendered_instant += 1; // we have rendered this instant.
            event!(Level::INFO, "-> done [playing]");

        }
    }

}

/// Module that performs the IO for the midi sequencer inside it.
/// Furthermore, it allows the track for the MIDI sequencer to be changed,
/// as well as changing playback settings (e.g. part of sequencer to loop).
struct MidiSequencerIO {
    sequencer : Arc<Mutex<MidiSequencer>>,
    params : OutputDeviceParameters,
    device : Box <dyn BaseAudioOutputDevice>
}

impl MidiSequencerIO {
    fn new(sequencer : MidiSequencer, params : OutputDeviceParameters) -> Self {
        let sequencer = Arc::new(Mutex::new(sequencer));
        // The output buffer (3 seconds).
        let mut left: Vec<f32> = vec![0_f32; params.channel_sample_count];
        let mut right: Vec<f32> = vec![0_f32; params.channel_sample_count];
        let mut t = 0;
        let device : Box <dyn BaseAudioOutputDevice> = run_output_device(params, {
            let sequencer = sequencer.clone();
            move |data| {
                event!(Level::INFO, "running audio device");
                sequencer.lock().as_mut().unwrap().process_and_render(&mut left[..], &mut right[..]);

                for i in 0..data.len() {
                    if i % 2 == 0 {
                        data[i] = left[i / 2];
                    } else {
                        data[i] = right[i / 2];
                    }
                }
            }
        })
        .unwrap();
        MidiSequencerIO {
            sequencer : sequencer.clone(),
            params :  params,
            device : device
        }
    }

    fn toggle_is_playing(&mut self) {
        self.sequencer.lock().as_mut().unwrap().toggle_is_playing();
    }

    fn restart(&mut self) {
        event!(Level::INFO, "### restarting ###");
        let mut seq_changer = self.sequencer.lock().unwrap();
        seq_changer.playing = true;
        seq_changer.cur_instant = 0;
        seq_changer.last_rendered_instant = 0;
    }

    fn set_track(&mut self, track : monodroneffi::Track) {
        self.sequencer.lock().as_mut().unwrap().track = track;
    }

}

fn main() {
    tracing_subscriber::fmt().init();
    let _ = tracing::subscriber::set_global_default(
        tracing_subscriber::registry()
        .with(tracing_tracy::TracyLayer::default()));

    let options = eframe::NativeOptions {
        // viewport: egui::ViewportBuilder::default().with_maximized(true),
        // .with_fullscreen(true),
        ..Default::default()
    };

    unsafe {
        event!(Level::INFO, "initializing lean runtime module");
        leanffi::lean_initialize_runtime_module();

        event!(Level::INFO, "initializing monodrone");
        monodroneffi::initialize();

        event!(Level::INFO, "done with Lean initialization. Marking end of initialization.");
        leanffi::lean_io_mark_end_initialization();
    }

    event!(Level::INFO, "creating context");
    let mut monodrone_ctx = monodroneffi::new_context();
    event!(Level::INFO, "ctx: {:p}", monodrone_ctx);
    let track = monodroneffi::get_track(monodrone_ctx);
    event!(Level::INFO, "track: {:?}", track);

    let sf2 = include_bytes!("../resources/TimGM6mb.sf2");
    let mut sf2_cursor = std::io::Cursor::new(sf2);
    // Load the SoundFont.
    let sound_font = Arc::new(SoundFont::new(&mut sf2_cursor).unwrap());


    let params = OutputDeviceParameters {
        channels_count: 2,
        sample_rate: 44100,
        channel_sample_count: 4410,
    };


    // Create the MIDI file sequencer.
    let settings = SynthesizerSettings::new(params.sample_rate as i32);
    let synthesizer = Synthesizer::new(&sound_font, &settings).unwrap();
    let mut sequencer_io : MidiSequencerIO = MidiSequencerIO::new(MidiSequencer::new(synthesizer), params);

    
    event!(Level::INFO, "Starting up");
    let (mut rl, thread) = raylib::init()
        .size(640, 480)
        .title("Hello, World")
        .build();


    while !rl.window_should_close() {
        let track = monodroneffi::get_track(monodrone_ctx);
        // event!(Level::INFO, "track: {:?}", track);

        if rl.is_key_pressed(KeyboardKey::KEY_SPACE) {
            sequencer_io.set_track(track.clone());
            sequencer_io.restart();
        }

        if rl.is_key_pressed(KeyboardKey::KEY_DOWN) {
            monodrone_ctx = monodroneffi::move_down_one(monodrone_ctx);
        } else if (rl.is_key_pressed(KeyboardKey::KEY_UP)) {
            monodrone_ctx = monodroneffi::move_up_one(monodrone_ctx);
        } else if (rl.is_key_pressed(KeyboardKey::KEY_C)) {
            monodrone_ctx = monodroneffi::add_note_c(monodrone_ctx);
        } else if (rl.is_key_pressed(KeyboardKey::KEY_J)) {
            monodrone_ctx = monodroneffi::lower_semitone(monodrone_ctx);
        } else if (rl.is_key_pressed(KeyboardKey::KEY_K)) {
            monodrone_ctx = monodroneffi::raise_semitone(monodrone_ctx);
        }


        let mut d = rl.begin_drawing(&thread);

        d.clear_background(Color::new(50, 50, 60, 255));
        

        // draw tracker.
        for y in 0..100 {
            let h = 1;
            d.draw_rectangle(4, 44 * y, 100, 40 * h, Color::GRAY);
        }

        for note in track.notes.iter() {
            let y = note.start as i32;
            let h = note.nsteps as i32;
            let pitch = note.pitch as i32;
            d.draw_rectangle(4, y, 8, 40 * h, Color::new(255, 166, 47, 255));
            d.draw_text(&format!(" {}", pitch), 10, 12, 22, Color::new(202, 244, 255, 255));
        }
    }
}