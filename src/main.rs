#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")] // hide console window on Windows in release
#![allow(rustdoc::missing_crate_level_docs)] // it's an example

use egui::epaint::text::cursor;
use egui::Key;
use ffi::{GetScreenHeight, GetScreenWidth};
use lean_sys::{
    lean_box, lean_inc_ref, lean_initialize_runtime_module, lean_io_mark_end_initialization,
};
use rand::seq::SliceRandom; // 0.7.2
use midi::Message::Start;
use monodroneffi::PlayerNote;
use raylib::prelude::*;
use std::borrow::BorrowMut;
use std::collections::HashMap;
use std::env;
use std::error::Error;
use std::process::Output;
use std::sync::Mutex;
use std::{fs::File, sync::Arc};
use tinyaudio::prelude::*;
use tinyaudio::{run_output_device, OutputDeviceParameters};
use rfd::FileDialog;


const GOLDEN_RATIO: f32 = 1.61803398875;

use midir::{Ignore, MidiInput};
use rustysynth::{MidiFile, MidiFileSequencer, SoundFont, Synthesizer, SynthesizerSettings};
use std::io::{stdin, stdout, Write};
use tracing::{event, Level};
use tracing_subscriber::layer::SubscriberExt;

mod monodroneffi;

use std::cmp::{self, max};


fn whimsical_file_name() -> String {
    let cool_nouns = vec![
        "griffin",
        "chimera",
        "phoenix",
        "dragon",
        "unicorn",
        "pegasus",
        "sphinx",
        "minotaur",
        "centaur",
        "tengu",
        "kappa",
        "kitsune",
        "oni",
        "yamauba",
        "yokai",
        "amaterasu",
        "susano",
    ];

    let cool_adjectives = vec![
        "golden",
        "silver",
        "crimson",
        "azure",
        "emerald",
        "lunar",
        "solar",
        "celestial",
        "earthly",
        "mystic",
        "fearsome",
        "terrifying",
        "magnificent",
        "divine",
        "sacred",
        "profane",
        "demonic",
        "eldritch",
        "sylvan",
        "escathonic",
        "cosmic",
        "abyssal",
        "infernal",
    ];

    // events-of-adjective-noun
    // lighting-of-mystic-dragon
    let events = vec![
        "lighting",
        "summoning",
        "banishment",
        "binding",
        "unleashing",
        "awakening",
        "calling",
        "sealing",
        "unsealing",
        "breaking",
        "shattering",
        "revealing",
        "concealing",
        "slaying",
        "vanquishing",
        "reanimation",
        "resurrection",
        "rebirth",
        "spellcasting",
        "hexing",
        "cursing",
    ];

    // choose a random event, random adjective, random noun and concatenate them in kebab case
    let mut rng = rand::thread_rng();
    let random_event = events.choose(&mut rng).unwrap();
    let random_adjective = cool_adjectives.choose(&mut rng).unwrap();
    let random_noun = cool_nouns.choose(&mut rng).unwrap();

    format!(
        "{}-of-{}-{}",
        random_event, random_adjective, random_noun
    )
}
// TODO: read midi

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NoteEvent {
    NoteOn { pitch: u8, instant: u64 },
    NoteOff { pitch: u8, instant: u64 },
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
        Some(self.cmp(other))
    }
}

impl Ord for NoteEvent {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // compare tuple of (instant, pitch)
        (self.instant(), self.pitch()).cmp(&(other.instant(), other.pitch()))
    }
}

/// Get the note events at a given time instant.
fn track_get_note_events_at_time(
    track: &monodroneffi::PlayerTrack,
    instant: u64,
) -> Vec<NoteEvent> {
    let mut note_events = Vec::new();
    let mut ix2pitches: HashMap<u64, Vec<u64>> = HashMap::new();

    for note in track.notes.iter() {
        ix2pitches
            .entry(note.start)
            .or_insert(Vec::new())
            .push(note.pitch);
    }
    // only emit a note off if there is no same note in the next time step.
    // Otherwise, we hear a jarring of a note being "stacattod" where we
    // turn it off and on in the same instant.
    for note in track.notes.iter() {
        if (note.start + note.nsteps) == instant {
            let off_event = NoteEvent::NoteOff {
                pitch: note.pitch as u8,
                instant: instant as u64,
            };
            match ix2pitches.get(&(note.start + note.nsteps)) {
                Some(next_notes) => {
                    if !next_notes.contains(&note.pitch) {
                        note_events.push(off_event);
                    }
                }
                None => {
                    note_events.push(off_event);
                }
            }
        }
        if note.start == instant {
            note_events.push(NoteEvent::NoteOn {
                pitch: note.pitch as u8,
                instant: instant as u64,
            });
        }
    }
    note_events
}

pub struct MidiSequencer {
    synthesizer: Synthesizer,
    track: monodroneffi::PlayerTrack,
    playing: bool,
    start_instant: u64,
    end_instant: u64,
    cur_instant: f32,           // current instant of time, as we last heard.
    last_rendered_instant: u64, // instant of time we last rendered.
    looping: bool,
    num_instants_wait_before_loop: u64,
    instant_delta: f32, // how many instants we increment at each tick. each tick is called at 1/10 of a second.
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
            track: monodroneffi::PlayerTrack::new(),
            playing: false,
            cur_instant: 0.0,
            start_instant: 0,
            last_rendered_instant: 0,
            looping: false,
            end_instant: 0,
            num_instants_wait_before_loop: 0,
            instant_delta: 0.5,
        }
    }

    pub fn set_track(&mut self, track: monodroneffi::PlayerTrack) {
        assert!(!self.playing); // we cannot change the track while playing.
        self.track = track;
    }

    /// Stops playing. Keep current location.
    pub fn stop(&mut self) {
        self.synthesizer.reset();
        self.playing = false;
        self.cur_instant = 0.0;
        self.last_rendered_instant = 0;
    }

    pub fn start(&mut self, start_instant: u64, end_instant: u64, looping: bool) {
        self.playing = true;
        self.cur_instant = start_instant as f32;
        self.start_instant = start_instant;
        self.end_instant = end_instant;
        self.looping = looping;
        self.last_rendered_instant = start_instant;
    }

    fn process_and_render(&mut self, left: &mut [f32], right: &mut [f32]) {
        let new_instant = self.cur_instant + self.instant_delta;
        // event!(
        //     Level::INFO,
        //     "process_and_render cur({}) -> new({}) |
        //      last rendered({}) | end({}) is_playing({}) | looping ({})",
        //     self.cur_instant,
        //     new_instant,
        //     self.last_rendered_instant,
        //     self.end_instant,
        //     self.playing,
        //     self.looping
        // );

        self.synthesizer.render(&mut left[0..], &mut right[0..]);

        if (!self.playing) {
            return;
        }

        if self.cur_instant >= self.end_instant as f32 {
            if !self.looping {
                self.playing = false;
                return;
            }
            let NUM_INSTANTS_WAIT_BEFORE_LOOP = 2;
            self.num_instants_wait_before_loop += 1;
            if self.num_instants_wait_before_loop >= NUM_INSTANTS_WAIT_BEFORE_LOOP {
                self.cur_instant = self.start_instant as f32;
                self.last_rendered_instant = self.start_instant;
                self.playing = true;
                self.num_instants_wait_before_loop = 0;
            }
        } else {
            assert!(self.last_rendered_instant <= self.cur_instant as u64);
            assert!(self.cur_instant <= new_instant);
            self.cur_instant = new_instant;

            assert!(left.len() == right.len());
            assert!(left.len() >= self.synthesizer.get_block_size()); // we have enough space to render at least one block.

            while new_instant - self.last_rendered_instant as f32 >= 1.0 {
                let note_events =
                    track_get_note_events_at_time(&self.track, self.last_rendered_instant);
                for note_event in note_events.iter() {
                    event!(Level::INFO, "note_event: {:?}", note_event);
                    match note_event {
                        NoteEvent::NoteOff { pitch, .. } => {
                            self.synthesizer.note_off(0, *pitch as i32);
                        }
                        NoteEvent::NoteOn { pitch, .. } => {
                            self.synthesizer.note_on(0, *pitch as i32, 100);
                        }
                    }
                }
                self.last_rendered_instant += 1; // we have rendered this instant.
            }
        }
    }
}

struct Debouncer {
    time_to_next_event: f32,
    debounce_time_sec: f32,
}

impl Debouncer {
    fn new(debounce_time_sec: f32) -> Self {
        Self {
            time_to_next_event: 0.0,
            debounce_time_sec,
        }
    }

    fn add_time_elapsed(&mut self, time_elapsed: f32) {
        self.time_to_next_event += time_elapsed;
    }

    fn debounce(&mut self, val: bool) -> bool {
        let out = val && (self.time_to_next_event > self.debounce_time_sec);
        if (out) {
            self.time_to_next_event = 0.0;
        }
        return out;
    }
}

struct Easer {
    pub target: f32,
    cur: f32,
    pub damping: f32,
}

impl Easer {
    fn new(value: f32) -> Easer {
        Easer {
            target: value,
            cur: value,
            damping: 0.2,
        }
    }

    fn get(&self) -> f32 {
        self.cur
    }

    fn set(&mut self, value: f32) {
        self.target = value;
    }

    fn step(&mut self, dt: f32) {
        if (self.target - self.cur).abs() > 100.0 {
            self.cur = self.target;
        }
        self.cur = self.cur + ((self.target - self.cur) * self.damping);
        if (self.cur - self.target).abs() < 0.1 {
            self.cur = self.target;
        }
    }
}

struct Easer2d {
    pub target_x: f32,
    pub target_y: f32,
    pub cur_x: f32,
    pub cur_y: f32,
    pub damping: f32,
}

impl Easer2d {
    fn new(x: f32, y: f32) -> Easer2d {
        Easer2d {
            target_x: x,
            target_y: y,
            cur_x: x,
            cur_y: y,
            damping: 0.2,
        }
    }

    fn get(&self) -> (f32, f32) {
        (self.cur_x, self.cur_y)
    }

    fn set(&mut self, x: f32, y: f32) {
        self.target_x = x;
        self.target_y = y;
    }

    fn set_y(&mut self, y: f32) {
        self.target_y = y;
    }

    fn step(&mut self, dt: f32) {
        self.cur_x = self.cur_x + ((self.target_x - self.cur_x) * self.damping);
        self.cur_y = self.cur_y + ((self.target_y - self.cur_y) * self.damping);
    }
}

fn isControlKeyPressed(rl : &RaylibHandle) -> bool {
    rl.is_key_down(KeyboardKey::KEY_LEFT_SUPER) ||
    rl.is_key_down(KeyboardKey::KEY_LEFT_CONTROL) ||
    rl.is_key_down(KeyboardKey::KEY_RIGHT_CONTROL)
}

/// Module that performs the IO for the midi sequencer inside it.
/// Furthermore, it allows the track for the MIDI sequencer to be changed,
/// as well as changing playback settings (e.g. part of sequencer to loop).
struct MidiSequencerIO {
    sequencer: Arc<Mutex<MidiSequencer>>,
    params: OutputDeviceParameters,
    device: Box<dyn BaseAudioOutputDevice>,
}

impl MidiSequencerIO {
    fn new(sequencer: MidiSequencer, params: OutputDeviceParameters) -> Self {
        let sequencer = Arc::new(Mutex::new(sequencer));
        // The output buffer (3 seconds).
        let mut left: Vec<f32> = vec![0_f32; params.channel_sample_count];
        let mut right: Vec<f32> = vec![0_f32; params.channel_sample_count];
        let mut t = 0;
        let device: Box<dyn BaseAudioOutputDevice> = run_output_device(params, {
            let sequencer = sequencer.clone();
            move |data| {
                // event!(Level::INFO, "running audio device");
                sequencer
                    .lock()
                    .as_mut()
                    .unwrap()
                    .process_and_render(&mut left[..], &mut right[..]);

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
            sequencer: sequencer.clone(),
            params: params,
            device: device,
        }
    }

    fn is_playing(&self) -> bool {
        self.sequencer.lock().as_ref().unwrap().playing
    }

    fn stop(&mut self) {
        self.sequencer.lock().as_mut().unwrap().stop();
    }

    fn increase_playback_rate(&mut self) {
        let mut seq_changer = self.sequencer.lock().unwrap();
        seq_changer.instant_delta += 0.1;
    }

    fn reduce_playback_rate(&mut self) {
        let mut seq_changer = self.sequencer.lock().unwrap();
        seq_changer.instant_delta -= 0.1;
    }

    fn get_playback_speed(&self) -> f32 {
        self.sequencer.lock().as_ref().unwrap().instant_delta
    }

    fn restart(&mut self, start_instant: u64, end_instant: u64, looping: bool) {
        event!(Level::INFO, "### restarting ###");
        let mut seq_changer = self.sequencer.lock().unwrap();

        seq_changer.looping = looping;
        seq_changer.start_instant = start_instant;
        seq_changer.end_instant = end_instant;
        seq_changer.start(start_instant, end_instant, looping);
    }

    fn set_track(&mut self, track: monodroneffi::PlayerTrack) {
        self.sequencer.lock().as_mut().unwrap().track = track;
    }
}

fn mainLoop() {
    tracing_subscriber::fmt().init();
    let _ = tracing::subscriber::set_global_default(
        tracing_subscriber::registry().with(tracing_tracy::TracyLayer::default()),
    );

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

        event!(
            Level::INFO,
            "done with Lean initialization. Marking end of initialization."
        );
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
    let mut sequencer_io: MidiSequencerIO =
        MidiSequencerIO::new(MidiSequencer::new(synthesizer), params);

    event!(Level::INFO, "Starting up");
    let SCREEN_WIDTH = unsafe { GetScreenWidth() };
    let SCREEN_HEIGHT = unsafe { GetScreenHeight() };
    let (mut rl, thread) = raylib::init()
        .size(SCREEN_WIDTH, SCREEN_HEIGHT)
        .title("monodrone")
        .build();

    rl.set_window_size(rl.get_screen_width(), rl.get_screen_height());

    let TARGET_FPS = 60;
    rl.set_target_fps(TARGET_FPS);
    let SCREEN_HEIGHT = rl.get_screen_height();

    let mut debounceMovement = Debouncer::new(80.0 / 1000.0);
    let mut debounceUndo = Debouncer::new(150.0 / 1000.0);

    let mut cameraYEaser = Easer::new(0.0);
    let mut nowPlayingYEaser = Easer::new(0.0);
    let mut cursorEaser = Easer2d::new(0.0, 0.0);
    let mut selectAnchorEaser = Easer2d::new(0.0, 0.0);
    nowPlayingYEaser.damping = 0.5;
    while !rl.window_should_close() {
        let time_elapsed = rl.get_frame_time();
        debounceMovement.add_time_elapsed(time_elapsed);
        debounceUndo.add_time_elapsed(time_elapsed);

        // Step 2: Get stuff to render
        if monodroneffi::get_track_sync_index(monodrone_ctx) != track.sync_index {
            track = monodroneffi::UITrack::from_lean(monodrone_ctx);
            println!("-> got new track {:?}", track);
        }

        if monodroneffi::get_cursor_sync_index(monodrone_ctx) != selection.sync_index {
            selection = monodroneffi::Selection::from_lean(monodrone_ctx);
            println!("-> got new selection");
        }

        if rl.is_key_pressed(KeyboardKey::KEY_MINUS) {
            sequencer_io.reduce_playback_rate();
        } else if rl.is_key_pressed(KeyboardKey::KEY_EQUAL) {
            sequencer_io.increase_playback_rate();
        } else if rl.is_key_pressed(KeyboardKey::KEY_SPACE) {
            if sequencer_io.is_playing() {
                sequencer_io.stop();
            } else {
                sequencer_io.set_track(track.to_player_track().clone());
                let is_looping = rl.is_key_down(KeyboardKey::KEY_LEFT_SHIFT);

                let start_instant = if is_looping {
                    cmp::min(
                        cmp::min(selection.cursor_y, selection.anchor_y) as u64,
                        track.get_last_instant() as u64,
                    )
                } else {
                    if rl.is_key_down(KeyboardKey::KEY_LEFT_SHIFT) {
                        selection.cursor_y as u64
                    } else {
                        0
                    }
                };

                let end_instant = if is_looping {
                    cmp::max(
                        cmp::max(selection.cursor_y, selection.anchor_y) as u64,
                        track.get_last_instant() as u64,
                    )
                } else {
                    track.get_last_instant() as u64
                };
                sequencer_io.restart(start_instant, (end_instant + 1), is_looping);
            }
        } else if (debounceMovement.debounce(rl.is_key_down(KeyboardKey::KEY_J))) {

            if isControlKeyPressed(&rl) {
                monodrone_ctx = monodroneffi::drag_down_one(monodrone_ctx);
                // panic!("monodrone ctx drag down one");
            }


            if (rl.is_key_down(KeyboardKey::KEY_LEFT_SHIFT)) {
                monodrone_ctx = monodroneffi::select_anchor_move_down_one(monodrone_ctx);
            } else {
                monodrone_ctx = monodroneffi::cursor_move_down_one(monodrone_ctx);
            }
        } else if (debounceMovement.debounce(rl.is_key_down(KeyboardKey::KEY_K))) {

            if isControlKeyPressed(&rl) {
                monodrone_ctx = monodroneffi::drag_up_one(monodrone_ctx);
            }

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
        } else if (rl.is_key_pressed(KeyboardKey::KEY_C)) {
            monodrone_ctx = monodroneffi::set_pitch(monodrone_ctx, monodroneffi::PitchName::C);
        } else if (rl.is_key_pressed(KeyboardKey::KEY_D)) {
            monodrone_ctx = monodroneffi::set_pitch(monodrone_ctx, monodroneffi::PitchName::D);
        } else if (rl.is_key_pressed(KeyboardKey::KEY_E)) {
            monodrone_ctx = monodroneffi::set_pitch(monodrone_ctx, monodroneffi::PitchName::E);
        } else if (rl.is_key_pressed(KeyboardKey::KEY_F)) {
            monodrone_ctx = monodroneffi::set_pitch(monodrone_ctx, monodroneffi::PitchName::F);
        } else if (rl.is_key_pressed(KeyboardKey::KEY_G)) {
            monodrone_ctx = monodroneffi::set_pitch(monodrone_ctx, monodroneffi::PitchName::G);
        } else if (rl.is_key_pressed(KeyboardKey::KEY_A)) {
            monodrone_ctx = monodroneffi::set_pitch(monodrone_ctx, monodroneffi::PitchName::A);
        } else if (rl.is_key_pressed(KeyboardKey::KEY_B)) {
            monodrone_ctx = monodroneffi::set_pitch(monodrone_ctx, monodroneffi::PitchName::B);
        } else if (debounceMovement.debounce(rl.is_key_down(KeyboardKey::KEY_BACKSPACE))) {
            monodrone_ctx = monodroneffi::delete_line(monodrone_ctx);
        } else if (debounceUndo.debounce(rl.is_key_down(KeyboardKey::KEY_Z))) {
            // TODO: figure out how to get control key.
            if (rl.is_key_down(KeyboardKey::KEY_LEFT_SHIFT)) {
                monodrone_ctx = monodroneffi::redo_action(monodrone_ctx);
            } else {
                monodrone_ctx = monodroneffi::undo_action(monodrone_ctx);
            }
        } else if (rl.is_key_pressed(KeyboardKey::KEY_THREE)) {
            monodrone_ctx = monodroneffi::toggle_sharp(monodrone_ctx);
        } else if rl.is_key_pressed(KeyboardKey::KEY_TWO) {
            monodrone_ctx = monodroneffi::toggle_flat(monodrone_ctx);
        } else if (rl.is_key_pressed(KeyboardKey::KEY_COMMA)) {
            monodrone_ctx = monodroneffi::lower_octave(monodrone_ctx);
        } else if (rl.is_key_pressed(KeyboardKey::KEY_PERIOD)) {
            monodrone_ctx = monodroneffi::raise_octave(monodrone_ctx);
        } else if debounceMovement.debounce(rl.is_key_down(KeyboardKey::KEY_ENTER)) {
            monodrone_ctx = monodroneffi::newline(monodrone_ctx);
            monodrone_ctx = monodroneffi::cursor_move_down_one(monodrone_ctx);
        } else if (rl.is_key_pressed(KeyboardKey::KEY_S) && isControlKeyPressed(&rl)) {
            let saver_dialog = FileDialog::new()
                .add_filter("monodrone", &["drn"])
                .set_can_create_directories(true)
                .set_file_name(whimsical_file_name())
                .set_title("Save monodrone file location");

            let saver_dialog = if let Result::Ok(dir) = env::current_exe() {
                saver_dialog.set_directory(dir)
            } else { saver_dialog };

            if let Option::Some(path) = saver_dialog.save_file() {
                let str = monodroneffi::ctx_to_json_str(monodrone_ctx);
                // open file and write string.
                event!(Level::INFO, "saving file to path {path:?}");
                match File::create(path) {
                    Ok(mut file) => {
                        file.write_all(str.as_bytes()).unwrap();
                    }
                    Err(e) => {
                        event!(Level::ERROR, "error saving file: {:?}", e);
                    }
                }
            } else {
                event!(Level::INFO, "no path selected for save");
            }
        } else if rl.is_key_pressed(KeyboardKey::KEY_O) && isControlKeyPressed(&rl) {
            let open_dialog = FileDialog::new()
                .add_filter("monodrone", &["drn"])
                .set_can_create_directories(true)
                .set_title("Open monodrone file location");
            let open_dialog = if let Result::Ok(dir) = env::current_exe() {
                open_dialog.set_directory(dir)
            } else { open_dialog };

            if let Some(path) = open_dialog.pick_file() {
                // open path and load string.
                event!(Level::INFO, "loading file {path:?}");
                match File::open(path) {
                    Ok(file) => {
                        let reader = std::io::BufReader::new(file);
                        let str = std::io::read_to_string(reader).unwrap();
                        event!(Level::INFO, "loaded file data: {str}");
                        monodrone_ctx = monodroneffi::ctx_from_json_str(str);
                        track = monodroneffi::UITrack::from_lean(monodrone_ctx);
                        selection = monodroneffi::Selection::from_lean(monodrone_ctx);
                        event!(Level::INFO, "loaded file!");
                    }
                    Err(e) => {
                        event!(Level::ERROR, "error opening file: {:?}", e);
                    }
                }
            } else {
                event!(Level::INFO, "no path selected for open");
            }
        } else if rl.is_key_pressed(KeyboardKey::KEY_Q) && isControlKeyPressed(&rl) {
            break;
        }

        // Step 3: Render
        let mut d = rl.begin_drawing(&thread);

        d.clear_background(Color::new(33, 33, 33, 255));
        // d.clear_background(Color::new(38, 50, 56, 255));
        let BOX_HEIGHT = 40;
        let BOX_WIDTH = 40;
        let BOX_WIDTH_PADDING_LEFT = 5;
        let BOX_WINDOW_CORNER_PADDING_LEFT = BOX_WIDTH_PADDING_LEFT;
        let BOX_WIDTH_PADDING_RIGHT = 5;
        let BOX_HEIGHT_PADDING_TOP = 5;
        let BOX_WINDOW_CORNER_PADDING_TOP = BOX_HEIGHT_PADDING_TOP;
        let BOX_NOW_PLAYING_SUGAR_WIDTH = 5;

        let BOX_HEIGHT_PADDING_BOTTOM = 5;
        let BOX_DESLECTED_COLOR = Color::new(66, 66, 66, 255);
        let BOX_SELECTED_BACKGROUND_COLOR = Color::new(255, 0, 100, 255);
        let BOX_CURSORED_COLOR = Color::new(99, 99, 99, 255);
        let BOX_NOW_PLAYING_COLOR = Color::new(255, 143, 0, 255);
        let TEXT_COLOR_LEADING = Color::new(207, 216, 220, 255);
        let TEXT_COLLOR_FOLLOWING = Color::new(99, 99, 99, 255);
        let PLAYBACK_SPEED_TEXT_COLOR = Color::new(97, 97, 97, 255);

        let PLAYBACK_SPEED_INFO_Y = BOX_WINDOW_CORNER_PADDING_TOP;

        cameraYEaser.set(
            ((selection.anchor_y as f32
                * (BOX_HEIGHT + BOX_HEIGHT_PADDING_TOP + BOX_HEIGHT_PADDING_BOTTOM) as f32)
                - SCREEN_HEIGHT as f32 * 0.5)
                .max(0.0),
        );
        cameraYEaser.step(time_elapsed);

        cursorEaser.set(selection.cursor_x as f32, selection.cursor_y as f32);
        cursorEaser.damping = 0.3;
        cursorEaser.step(time_elapsed);

        selectAnchorEaser.set(selection.anchor_x as f32, selection.anchor_y as f32);
        selectAnchorEaser.damping = 0.2;
        selectAnchorEaser.step(time_elapsed);

        // draw tracker.
        {
            let cur_instant = sequencer_io.sequencer.lock().as_ref().unwrap().cur_instant;
            let now_playing_box_y = ((cur_instant as i32 - 1) as i32);

            nowPlayingYEaser.set(
                (BOX_WINDOW_CORNER_PADDING_TOP
                    + now_playing_box_y
                        * (BOX_HEIGHT + BOX_HEIGHT_PADDING_TOP + BOX_HEIGHT_PADDING_BOTTOM))
                    as f32,
            );
            nowPlayingYEaser.step(time_elapsed);
        }

        let logical_x_to_draw_x = |ix: f32| -> i32 {
            BOX_WINDOW_CORNER_PADDING_LEFT
                + (ix * (BOX_WIDTH + BOX_WIDTH_PADDING_LEFT + BOX_WIDTH_PADDING_RIGHT) as f32)
                    as i32
                + BOX_WIDTH_PADDING_LEFT
        };

        let logical_y_to_draw_y = |iy: f32| -> i32 {
            BOX_WINDOW_CORNER_PADDING_TOP
                + (iy * (BOX_HEIGHT + BOX_HEIGHT_PADDING_TOP + BOX_HEIGHT_PADDING_BOTTOM) as f32)
                    as i32
                + BOX_HEIGHT_PADDING_TOP
                - cameraYEaser.get() as i32
        };

        let logical_width_to_draw_width = |width: f32| -> i32 {
            (width * (BOX_WIDTH) as f32
                + (width - 1.0) * (BOX_WIDTH_PADDING_LEFT as f32 + BOX_WIDTH_PADDING_RIGHT as f32))
                as i32
        };

        let logical_height_to_draw_height = |height: f32| -> i32 {
            (height * (BOX_HEIGHT) as f32
                + (height - 1.0)
                    * (BOX_HEIGHT_PADDING_TOP as f32 + BOX_HEIGHT_PADDING_BOTTOM as f32))
                as i32
        };

        let cursor_draw_x = logical_x_to_draw_x(cursorEaser.get().0);
        let cursor_draw_y = logical_y_to_draw_y(cursorEaser.get().1);

        let select_anchor_draw_x = logical_x_to_draw_x(selectAnchorEaser.get().0);
        let select_anchor_draw_y = logical_y_to_draw_y(selectAnchorEaser.get().1);

        let top_left_draw_x = cursor_draw_x.min(select_anchor_draw_x);
        let top_left_draw_y = cursor_draw_y.min(select_anchor_draw_y);
        let bottom_right_draw_x = cursor_draw_x.max(select_anchor_draw_x);
        let bottom_right_draw_y = cursor_draw_y.max(select_anchor_draw_y);

        for x in 0u64..8 {
            for y in 0u64..100 {
                let draw_x = logical_x_to_draw_x(x as f32);
                let draw_y = logical_y_to_draw_y(y as f32);
                let draw_color = if x == selection.cursor_x && y == selection.cursor_y {
                    BOX_CURSORED_COLOR
                } else if top_left_draw_x <= draw_x
                    && (draw_x - bottom_right_draw_x) <= BOX_WIDTH / 5
                    && top_left_draw_y <= draw_y
                    && (draw_y - bottom_right_draw_y) <= BOX_HEIGHT / 5
                {
                    BOX_SELECTED_BACKGROUND_COLOR
                } else {
                    BOX_DESLECTED_COLOR
                };

                d.draw_rectangle(
                    draw_x as i32,
                    draw_y as i32,
                    BOX_WIDTH as i32,
                    BOX_HEIGHT as i32,
                    draw_color,
                );
            }
        }

        // selection is distinct from cursor, so draw it.
        if selection.cursor_x != selection.anchor_x || selection.cursor_y != selection.anchor_y {
            d.draw_rectangle(
                select_anchor_draw_x as i32,
                select_anchor_draw_y as i32,
                BOX_WIDTH as i32,
                BOX_HEIGHT as i32,
                BOX_SELECTED_BACKGROUND_COLOR,
            );
        }

        d.draw_rectangle(
            cursor_draw_x,
            cursor_draw_y,
            BOX_WIDTH as i32,
            BOX_HEIGHT as i32,
            BOX_CURSORED_COLOR,
        );

        for x in 0u64..8 {
            for y in 0u64..100 {
                let draw_x = logical_x_to_draw_x(x as f32);
                let draw_y = logical_y_to_draw_y(y as f32);

                match track.get_note_from_coord(x, y) {
                    Some(note) => {
                        let text_color = if (note.x == x && note.y == y) {
                            TEXT_COLOR_LEADING
                        } else {
                            TEXT_COLLOR_FOLLOWING
                        };
                        d.draw_text(
                            &format!("{}", note.to_str()),
                            draw_x as i32 + 5,
                            draw_y as i32 + 5,
                            20,
                            text_color,
                        );

                        let OCTAVE_TEXT_HEIGHT = 10;
                        let OCTAVE_TEXT_PADDING = 2;
                        let octave_text_len =
                            d.measure_text(&format!("{}", note.octave), OCTAVE_TEXT_HEIGHT);
                        d.draw_text(
                            &format!("{}", note.octave),
                            draw_x as i32 + BOX_WIDTH - octave_text_len - OCTAVE_TEXT_PADDING,
                            draw_y as i32 + BOX_HEIGHT - OCTAVE_TEXT_HEIGHT - OCTAVE_TEXT_PADDING,
                            OCTAVE_TEXT_HEIGHT,
                            Color::new(100, 255, 0, 255),
                        );
                    }
                    None => (),
                };
            }
        }

        d.draw_rectangle(
            0 as i32,
            (nowPlayingYEaser.get() - cameraYEaser.get()) as i32,
            BOX_NOW_PLAYING_SUGAR_WIDTH as i32,
            BOX_HEIGHT as i32,
            BOX_NOW_PLAYING_COLOR,
        );

        {
            let text = format!("Playback Speed: {:.1}", sequencer_io.get_playback_speed());
            let width = d.measure_text(text.as_str(), 20);
            d.draw_text(
                &text,
                d.get_screen_width() as i32 - width as i32 - 20,
                PLAYBACK_SPEED_INFO_Y,
                20,
                PLAYBACK_SPEED_TEXT_COLOR,
            );
        }
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
