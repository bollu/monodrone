#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")] // hide console window on Windows in release
#![allow(rustdoc::missing_crate_level_docs)] // it's an example

use std::borrow::BorrowMut;
use std::collections::HashMap;
use std::error::Error;
use std::process::Output;
use std::sync::Mutex;
use std::{fs::File, sync::Arc};
use egui::Key;
use lean_sys::{lean_io_mark_end_initialization, lean_initialize_runtime_module, lean_box, lean_inc_ref};
use midi::Message::Start;
use monodroneffi::PlayerNote;
use raylib::prelude::*;
use tinyaudio::{run_output_device, OutputDeviceParameters};
use tinyaudio::prelude::*;

const GOLDEN_RATIO: f32 = 1.61803398875;

use rustysynth::{MidiFile, MidiFileSequencer, SoundFont, Synthesizer, SynthesizerSettings};
use tracing_subscriber::layer::SubscriberExt;
use tracing::{event, Level};
use midir::{Ignore, MidiInput};
use std::io::{stdin, stdout, Write};


mod monodroneffi;

use std::cmp::{self, max};

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

const AUDIO_TIME_STRETCH_FACTOR : u64 = 1;

/// Get the note events at a given time instant.
fn track_get_note_events_at_time (track : &monodroneffi::PlayerTrack, instant : u64) -> Vec<NoteEvent> {
    let mut note_events = Vec::new();
    let mut ix2pitches : HashMap<u64, Vec<u64>> = HashMap::new();

    for note in track.notes.iter() {
        ix2pitches.entry(note.start).or_insert(Vec::new()).push(note.pitch);
    }
    // only emit a note off if there is no same note in the next time step.
    // Otherwise, we hear a jarring of a note being "stacattod" where we
    // turn it off and on in the same instant.
    for note in track.notes.iter() {
        if (note.start + note.nsteps) * AUDIO_TIME_STRETCH_FACTOR  == instant {
            let off_event = NoteEvent::NoteOff { pitch : note.pitch as u8, instant : instant as u64 };
            match ix2pitches.get(&(note.start+note.nsteps)) {
                Some(next_notes) => {
                    if !next_notes.contains(&note.pitch) {
                        note_events.push(off_event);
                    }
                },
                None => {
                    note_events.push(off_event);
                }
            }
        }
        if note.start * AUDIO_TIME_STRETCH_FACTOR == instant {
            note_events.push(NoteEvent::NoteOn { pitch : note.pitch as u8, instant : instant as u64 });
        }
    }
    note_events
}

pub struct MidiSequencer {
    synthesizer: Synthesizer,
    track : monodroneffi::PlayerTrack,
    playing : bool,
    start_instant : u64,
    end_instant : u64,
    cur_instant : u64, // current instant of time, as we last heard.
    last_rendered_instant : u64, // instant of time we last rendered.
    looping : bool,
    num_instants_wait_before_loop : u64,
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
            track : monodroneffi::PlayerTrack::new(),
            playing: false,
            cur_instant: 0,
            start_instant: 0,
            last_rendered_instant: 0,
            looping : false,
            end_instant : 0,
            num_instants_wait_before_loop : 0,
        }
    }

    pub fn set_track(&mut self, track : monodroneffi::PlayerTrack) {
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
        self.cur_instant = 0;
        self.last_rendered_instant = 0;
    }

    pub fn start(&mut self, start_instant : u64, end_instant : u64, looping : bool) {
        self.playing = true;
        self.cur_instant = start_instant;
        self.start_instant = start_instant;
        self.end_instant = end_instant;
        self.looping = looping;
        self.last_rendered_instant = start_instant;
    }

    fn process_and_render(&mut self, left: &mut [f32], right: &mut [f32]) {
        // TODO: do this based on time elapsed. This seems to be called
        // per "instant" that a new note needs to be played, as per
        let new_instant = self.cur_instant + 1;
        event!(Level::INFO, "process_and_render cur({}) -> new({}) |
             last rendered({}) | end({}) is_playing({}) | looping ({})",
        self.cur_instant, new_instant, self.last_rendered_instant,
        self.end_instant, self.playing, self.looping);


        if !self.playing {
            left.fill(0f32);
            right.fill(0f32);

            if self.looping {
                println!("looping");
                let NUM_INSTANTS_WAIT_BEFORE_LOOP = 2;
                self.num_instants_wait_before_loop += 1;
                if self.num_instants_wait_before_loop >= NUM_INSTANTS_WAIT_BEFORE_LOOP {
                    self.cur_instant = self.start_instant;
                    self.last_rendered_instant = self.start_instant;
                    self.playing = true;
                    self.num_instants_wait_before_loop = 0;
                }
            }
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
            // event!(Level::INFO, "-> done [playing]");

        }

        if self.cur_instant >= self.end_instant {
            self.playing = false;
        }


    }

}

struct Debouncer {
    time_to_next_event : f32,
    debounce_time_sec : f32,
}

impl Debouncer {
    fn new(debounce_time_sec : f32) -> Self {
        Self {
            time_to_next_event : 0.0,
            debounce_time_sec
        }
    }

    fn add_time_elapsed(&mut self, time_elapsed : f32) {
        self.time_to_next_event += time_elapsed;
    }

    fn debounce(&mut self, val : bool) -> bool {
        let out = val && (self.time_to_next_event > self.debounce_time_sec);
        if (out) {
            self.time_to_next_event = 0.0;
        }
        return out

    }

}

struct Easer  {
    pub target : f32,
    cur : f32,
    pub damping : f32
}

impl Easer {
    fn new(value : f32) -> Easer {
        Easer {
            target : value,
            cur : value,
            damping : 0.2,
        }
    }

    fn get(&self) -> f32 {
        self.cur
    }

     fn set (&mut self, value : f32) {
        self.target = value;
     }

    fn step (&mut self, dt : f32) {
        if (self.target - self.cur).abs() > 100.0 {
            self.cur = self.target;
        }
        self.cur = self.cur + ((self.target - self.cur) * self.damping);
        if (self.cur - self.target).abs() < 0.1 {
            self.cur = self.target;
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
                // event!(Level::INFO, "running audio device");
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

    fn restart(&mut self, start_instant : u64, end_instant : u64, looping : bool) {
        event!(Level::INFO, "### restarting ###");
        let mut seq_changer = self.sequencer.lock().unwrap();

        seq_changer.looping = looping;
        seq_changer.start_instant = start_instant;
        seq_changer.end_instant = end_instant;
        if seq_changer.playing {
            seq_changer.stop()
        } else {
            seq_changer.start(start_instant, end_instant, looping);

        }
    }

    fn set_track(&mut self, track : monodroneffi::PlayerTrack) {
        self.sequencer.lock().as_mut().unwrap().track = track;
    }

}


fn mainLoop() {
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
        lean_initialize_runtime_module();

        event!(Level::INFO, "initializing monodrone");
        monodroneffi::initialize();

        event!(Level::INFO, "done with Lean initialization. Marking end of initialization.");
        lean_io_mark_end_initialization();
    }

    event!(Level::INFO, "creating context");
    let mut monodrone_ctx = monodroneffi::new_context();

    let mut track = monodroneffi::UITrack::from_lean(monodrone_ctx);
    event!(Level::INFO, "track: {:?}", track);
    let mut selection = monodroneffi::Selection::from_lean(monodrone_ctx);
    event!(Level::INFO, "selection: {:?}", selection);

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

    let TARGET_FPS = 60;
    rl.set_target_fps(TARGET_FPS);
    let SCREEN_HEIGHT = rl.get_screen_height();

    let mut debounceMovement = Debouncer::new(80.0 / 1000.0);

    let mut cameraYEaser = Easer::new(0.0);
    let mut nowPlayingYEaser = Easer::new(0);
    nowPlayingYEaser.damping = 0.5;
    while !rl.window_should_close() {
        let time_elapsed = rl.get_frame_time();
        debounceMovement.add_time_elapsed(time_elapsed);

        // Step 2: Get stuff to render
        if monodroneffi::get_track_sync_index(monodrone_ctx) != track.sync_index {
            track = monodroneffi::UITrack::from_lean(monodrone_ctx);
            println!("-> got new track {:?}", track);
        }

        if monodroneffi::get_cursor_sync_index(monodrone_ctx) != selection.sync_index {
            selection = monodroneffi::Selection::from_lean(monodrone_ctx);
            println!("-> got new selection");
        }


        if rl.is_key_pressed(KeyboardKey::KEY_SPACE) {

            sequencer_io.set_track(track.to_player_track().clone());
            let is_looping =
                selection.cursor_y != selection.anchor_y;
            let start_instant = if is_looping {
                cmp::min(selection.cursor_y, selection.anchor_y) as u64
            } else {
                if rl.is_key_down(KeyboardKey::KEY_LEFT_SHIFT) {
                    selection.cursor_y as u64
                } else {
                    0
                }
            };

            let end_instant = if is_looping {
                cmp::max(selection.cursor_y, selection.anchor_y) as u64
            } else {
                track.get_last_instant() as u64
            };
            sequencer_io.restart(start_instant * AUDIO_TIME_STRETCH_FACTOR,
                end_instant * AUDIO_TIME_STRETCH_FACTOR,
                is_looping);
        } else if (debounceMovement.debounce(rl.is_key_down(KeyboardKey::KEY_J))) {
            if ( rl.is_key_down(KeyboardKey::KEY_LEFT_SHIFT)) {
                monodrone_ctx = monodroneffi::select_anchor_move_down_one(monodrone_ctx);
            } else {
                monodrone_ctx = monodroneffi::cursor_move_down_one(monodrone_ctx);
            }
        } else if (debounceMovement.debounce(rl.is_key_down(KeyboardKey::KEY_K))) {
            if (rl.is_key_down(KeyboardKey::KEY_LEFT_SHIFT)) {
                monodrone_ctx = monodroneffi::select_anchor_move_up_one(monodrone_ctx);
            } else {
                monodrone_ctx = monodroneffi::cursor_move_up_one(monodrone_ctx);
            }
        } else if (debounceMovement.debounce(rl.is_key_down(KeyboardKey::KEY_H))) {
            if (rl.is_key_down(KeyboardKey::KEY_LEFT_SHIFT)) {
                monodrone_ctx = monodroneffi::select_anchor_move_left_one(monodrone_ctx);
            } else {
                monodrone_ctx = monodroneffi::cursor_move_left_one(monodrone_ctx);
            }
        } else if (debounceMovement.debounce(rl.is_key_down(KeyboardKey::KEY_L))) {
            if (rl.is_key_down(KeyboardKey::KEY_LEFT_SHIFT)) {
                monodrone_ctx = monodroneffi::select_anchor_move_right_one(monodrone_ctx);
            } else {
                monodrone_ctx = monodroneffi::cursor_move_right_one(monodrone_ctx);
            }

        }
        else if (rl.is_key_pressed(KeyboardKey::KEY_C)) {
            monodrone_ctx = monodroneffi::set_pitch(monodrone_ctx, monodroneffi::PitchName::C);
        }
        else if (rl.is_key_pressed (KeyboardKey::KEY_D)) {
            monodrone_ctx = monodroneffi::set_pitch(monodrone_ctx, monodroneffi::PitchName::D);
        }
        else if (rl.is_key_pressed (KeyboardKey::KEY_E)) {
            monodrone_ctx = monodroneffi::set_pitch(monodrone_ctx, monodroneffi::PitchName::E);
        }
        else if (rl.is_key_pressed (KeyboardKey::KEY_F)) {
            monodrone_ctx = monodroneffi::set_pitch(monodrone_ctx, monodroneffi::PitchName::F);
        }
        else if (rl.is_key_pressed (KeyboardKey::KEY_G)) {
            monodrone_ctx = monodroneffi::set_pitch(monodrone_ctx, monodroneffi::PitchName::G);
        }
        else if (rl.is_key_pressed (KeyboardKey::KEY_A)) {
            monodrone_ctx = monodroneffi::set_pitch(monodrone_ctx, monodroneffi::PitchName::A);
        }
        else if (rl.is_key_pressed (KeyboardKey::KEY_B)) {
            monodrone_ctx = monodroneffi::set_pitch(monodrone_ctx, monodroneffi::PitchName::B);
        } else if (rl.is_key_pressed(KeyboardKey::KEY_BACKSPACE)) {
            monodrone_ctx = monodroneffi::delete(monodrone_ctx);
        }
        else if (rl.is_key_pressed(KeyboardKey::KEY_Z)) { // TODO: figure out how to get control key.
            if (rl.is_key_down(KeyboardKey::KEY_LEFT_SHIFT)) {
                    monodrone_ctx = monodroneffi::redo_action(monodrone_ctx);
            } else {
                println!("undo");
                monodrone_ctx = monodroneffi::undo_action(monodrone_ctx);
            }
        }
        else if (rl.is_key_pressed(KeyboardKey::KEY_THREE)) {
            monodrone_ctx = monodroneffi::toggle_sharp(monodrone_ctx);
        } else if rl.is_key_pressed(KeyboardKey::KEY_TWO) {
            monodrone_ctx = monodroneffi::toggle_flat(monodrone_ctx);
        }

        // Step 3: Render
        let mut d = rl.begin_drawing(&thread);

        d.clear_background(Color::new(50, 50, 60, 255));

        let BOX_HEIGHT = 40;
        let BOX_WIDTH = 40;
        let BOX_WIDTH_PADDING_LEFT = 5;
        let BOX_WINDOW_CORNER_PADDING_LEFT = BOX_WIDTH_PADDING_LEFT;
        let BOX_WIDTH_PADDING_RIGHT = 5;
        let BOX_HEIGHT_PADDING_TOP = 5;
        let BOX_WINDOW_CORNER_PADDING_TOP = BOX_HEIGHT_PADDING_TOP;
        let BOX_NOW_PLAYING_SUGAR_WIDTH = 5;

        let BOX_HEIGHT_PADDING_BOTTOM = 5;
        let BOX_DESLECTED_COLOR = Color::new(100, 100, 100, 255);
        let BOX_SELECTED_COLOR = Color::new(180, 180, 180, 255);
        let BOX_CURSORED_COLOR = Color::new(255, 255, 255, 255);
        let BOX_NOW_PLAYING_COLOR = Color::new(255, 143, 0, 255);
        let TEXT_COLOR_LEADING = Color::new(0, 0, 0, 255);
        let TEXT_COLLOR_FOLLOWING = Color::new(120, 120, 120, 255);

        cameraYEaser.set(
            (((selection.anchor_y as f32 *
            (BOX_HEIGHT + BOX_HEIGHT_PADDING_TOP + BOX_HEIGHT_PADDING_BOTTOM) as f32)) -
            SCREEN_HEIGHT as f32 * 0.5).max(0.0));
        cameraYEaser.step(time_elapsed);
        // draw tracker.
        {
            let cur_instant = sequencer_io.sequencer.lock().as_ref().unwrap().cur_instant;
            let now_playing_box_y =
                (cur_instant as i32 / AUDIO_TIME_STRETCH_FACTOR as i32);

            nowPlayingYEaser.set(
                (BOX_WINDOW_CORNER_PADDING_LEFT +
                now_playing_box_y * (BOX_HEIGHT + BOX_HEIGHT_PADDING_TOP + BOX_HEIGHT_PADDING_BOTTOM))
                as f32
            );
            nowPlayingYEaser.step(time_elapsed);

        }
        for x in 0u64..8 {
            for y in 0u64..100 {
                let draw_x = BOX_WINDOW_CORNER_PADDING_LEFT +
                    x as i32 * (BOX_WIDTH + BOX_WIDTH_PADDING_LEFT + BOX_WIDTH_PADDING_RIGHT) +
                    BOX_WIDTH_PADDING_LEFT;
                let draw_y = BOX_WINDOW_CORNER_PADDING_TOP +
                    y as i32 * (BOX_HEIGHT + BOX_HEIGHT_PADDING_TOP + BOX_HEIGHT_PADDING_BOTTOM) +
                    BOX_HEIGHT_PADDING_TOP - cameraYEaser.get() as i32;
                let mut draw_color =
                if (selection.is_cursored(x, y)) {
                    BOX_CURSORED_COLOR
                }
                else if (selection.is_selected(x, y)) {
                    BOX_SELECTED_COLOR
                }
                else {
                    BOX_DESLECTED_COLOR
                };
                d.draw_rectangle(draw_x as i32,
                    draw_y as i32,
                    BOX_WIDTH as i32,
                    BOX_HEIGHT as i32, draw_color);

                match track.get_note_from_coord(x, y) {
                    Some(note) => {
                        let text_color = if (note.x == x && note.y == y) {
                            TEXT_COLOR_LEADING
                        } else {
                            TEXT_COLLOR_FOLLOWING
                        };
                        d.draw_text(&format!("{}", note.to_str()),
                                draw_x as i32 + 5, draw_y as i32 + 5, 20,
                                text_color);
                    },
                    None => ()
                };
            }
        }

        d.draw_rectangle(0 as i32,
            (nowPlayingYEaser.get() - cameraYEaser.get()) as i32,
            BOX_NOW_PLAYING_SUGAR_WIDTH as i32,
            BOX_HEIGHT as i32, BOX_NOW_PLAYING_COLOR);

    }
}

fn testMidiInOpZ() -> Result<(), Box<dyn Error>> {
    let mut input = String::new();

    let mut midi_in = MidiInput::new("midir reading input")?;
    midi_in.ignore(Ignore::None);

    // Get an input port (read from console if multiple are available)
    let in_ports = midi_in.ports();
    let in_port = match in_ports.len() {
        0 => return Err("no input port found".into()),
        1 => {
            println!(
                "Choosing the only available input port: {}",
                midi_in.port_name(&in_ports[0]).unwrap()
            );
            &in_ports[0]
        }
        _ => {
            println!("\nAvailable input ports:");
            for (i, p) in in_ports.iter().enumerate() {
                println!("{}: {}", i, midi_in.port_name(p).unwrap());
            }
            print!("Please select input port: ");
            stdout().flush()?;
            let mut input = String::new();
            stdin().read_line(&mut input)?;
            in_ports
                .get(input.trim().parse::<usize>()?)
                .ok_or("invalid input port selected")?
        }
    };

    println!("\nOpening connection");
    let in_port_name = midi_in.port_name(in_port)?;

    // _conn_in needs to be a named parameter, because it needs to be kept alive until the end of the scope
    let _conn_in = midi_in.connect(
        in_port,
        "midir-read-input",
        move |stamp, message, _| {
            println!("{}: {:?} (len = {})", stamp, message, message.len());
        },
        (),
    )?;

    println!(
        "Connection open, reading input from '{}' (press enter to exit) ...",
        in_port_name
    );

    input.clear();
    stdin().read_line(&mut input)?; // wait for next enter key press

    println!("Closing connection");
    Ok(())
}


fn main() {
    // match testMidiInOpZ() {
    //     Ok(_) => (),
    //     Err(err) => println!("Error: {}", err),
    // };
    mainLoop();
}
