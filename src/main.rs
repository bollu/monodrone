#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")] // hide console window on Windows in release
#![allow(rustdoc::missing_crate_level_docs)] // it's an example

use directories::{BaseDirs, ProjectDirs, UserDirs};
use egui::epaint::text::cursor;
use egui::Key;
use lean_sys::{
    lean_box, lean_inc_ref, lean_initialize_runtime_module, lean_io_mark_end_initialization,
};
use std::ffi::OsStr; // https://github.com/tauri-apps/muda

use midi::Message::Start;
use monodroneffi::{PlayerNote, TrackBuilder, UITrack};
use rand::seq::SliceRandom; // 0.7.2
use rfd::FileDialog;
use std::collections::HashMap;
use std::env;
use std::error::Error;
use std::path::{Path, PathBuf};
use std::process::Output;
use std::sync::Mutex;
use std::{fs::File, sync::Arc};
use tinyaudio::prelude::*;
use tinyaudio::{run_output_device, OutputDeviceParameters};
use eframe::egui;
use egui::*;


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

    format!("{}-of-{}-{}", random_event, random_adjective, random_noun)
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

    // fn to_midi_message(self) -> midly::MidiMessage {
    //     match self {
    //         NoteEvent::NoteOn { pitch, .. } => midly::TrackEventKind::Midi {
    //             channel: midly::num::u4::from_int_lossy(0),
    //             message: midly::MidiMessage::NoteOn {
    //                 key: midly::num::u7::from_int_lossy(pitch),
    //                 vel: midly::num::u7::from_int_lossy(100),
    //             },
    //         },
    fn to_midi_message(self) -> midly::MidiMessage {
        match self {
            NoteEvent::NoteOn { pitch, .. } =>  {
                midly::MidiMessage::NoteOn {
                    key: midly::num::u7::from_int_lossy(pitch),
                    vel: midly::num::u7::from_int_lossy(100),
                }
            },
            NoteEvent::NoteOff { pitch, .. } =>  {
                midly::MidiMessage::NoteOff {
                    key: midly::num::u7::from_int_lossy(pitch),
                    vel: midly::num::u7::from_int_lossy(100),
                }
            }
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

        if !self.playing {
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
        if out { self.time_to_next_event = 0.0; }
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

    fn step(&mut self, _dt: f32) {
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

    fn step(&mut self, _dt: f32) {
        self.cur_x = self.cur_x + ((self.target_x - self.cur_x) * self.damping);
        self.cur_y = self.cur_y + ((self.target_y - self.cur_y) * self.damping);
    }
}

// fn is_control_key_down(rl: &RaylibHandle) -> bool {
//     rl.is_key_down(KeyboardKey::KEY_LEFT_SUPER)
//         || rl.is_key_down(KeyboardKey::KEY_LEFT_CONTROL)
//         || rl.is_key_down(KeyboardKey::KEY_RIGHT_CONTROL)
// }
//
// fn is_shift_key_down(rl: &RaylibHandle) -> bool {
//     rl.is_key_down(KeyboardKey::KEY_LEFT_SHIFT) || rl.is_key_down(KeyboardKey::KEY_RIGHT_SHIFT)
// }

#[derive(Clone, Eq, PartialEq, PartialOrd, Ord, Debug)]
struct AppFilePath {
    path: PathBuf,
}

impl AppFilePath {
    //fn new_whimsical(rl: &RaylibHandle, thread: &RaylibThread) -> AppFilePath {
    fn new_whimsical() -> AppFilePath {
        let mut filename = whimsical_file_name();
        filename.push_str(".drn");
        let mut out = directories::UserDirs::new().unwrap().audio_dir().unwrap().to_path_buf();
        out.push("Monodrone");
        std::fs::create_dir_all(&out).unwrap();
        out.push(filename);
        // AppFilePath::_format_and_set_window_title(&out.as_path(), &rl, &thread);
        AppFilePath { path: out }
    }

    fn parent_dir(&self) -> &Path {
        self.path.parent().unwrap()
    }

    fn file_stem(&self) -> &OsStr {
        self.path.file_stem().unwrap()
    }

    // fn set_file_path(&mut self, rl: &RaylibHandle, thread: &RaylibThread, path: &Path) {
    fn set_file_path(&mut self, path: &Path) {
        self.path = path.to_path_buf();
        // AppFilePath::_format_and_set_window_title(&path, &rl, &thread);
    }

    fn get_export_file_path(&self) -> PathBuf {
        let mut out = self.path.clone();
        out.pop();
        out.push(self.file_stem().to_string_lossy().to_string() + ".mid");
        out
    }

    // fn _format_and_set_window_title(path: &Path, rl: &RaylibHandle, thread: &RaylibThread) {
    //     rl.set_window_title(
    //         thread,
    //         format!("monodrone ({})", path.to_string_lossy()).as_str(),
    //     )
    // }

    fn to_string(&self) -> String {
        self.path.to_string_lossy().to_string()
    }
}

impl AsRef<Path> for AppFilePath {
    fn as_ref(&self) -> &Path {
        &self.path
    }
}
impl Into<String> for AppFilePath {
    fn into(self) -> String {
        self.to_string()
    }
}

#[derive(Debug)]
struct SequenceNumbered<T> {
    seq: u64,
    value: T,
}

impl<T> SequenceNumbered<T> {
    fn new(value: T) -> Self {
        Self {
            seq: 0,
            value: value,
        }
    }

    fn update_seq(&mut self, seq: u64) -> bool {
        let updated = seq != self.seq;
        self.seq = seq;
        return updated;
    }

    fn set_value(&mut self, value: T) {
        self.value = value;
    }
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

    fn set_playback_rate(&mut self, instant_delta: f32) {
        let mut seq_changer = self.sequencer.lock().unwrap();
        seq_changer.instant_delta = instant_delta;
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

fn save (monodrone_ctx : *mut lean_sys::lean_object, track : &UITrack, cur_filepath : &AppFilePath) {
    let str = monodroneffi::ctx_to_json_str(monodrone_ctx);
    event!(Level::INFO, "saving file to path: '{}'", cur_filepath.to_string());
    match File::create(cur_filepath.path.as_path()) {
        Ok(mut file) => {
            file.write_all(str.as_bytes()).unwrap();
            event!(Level::INFO, "Successfully saved '{}'", cur_filepath.to_string());

        }
        Err(e) => {
            event!(Level::ERROR, "Error saving file: {:?}", e);
            rfd::MessageDialog::new()
                .set_level(rfd::MessageLevel::Error)
                .set_title(format!(
                    "Unable to save file to path '{}'.",
                    cur_filepath.to_string()
                ))
                .set_description(e.to_string())
                .show();
        }
    };
    let midi_filepath = cur_filepath.get_export_file_path();
    let midi_file = match File::create(midi_filepath.clone()) {
        Ok(file) => file,
        Err(e) => {
            rfd::MessageDialog::new()
                .set_level(rfd::MessageLevel::Error)
                .set_title("Unable to create MIDI file")
                .set_description(e.to_string())
                .show();
            event!(Level::ERROR, "error creating MIDI file: {:?}", e);
            return;
        }
    };
    let player_track = track.to_player_track();
    let (header, tracks) = player_track.to_smf();
    match midly::write_std(&header, tracks.iter(), midi_file) {
        Ok(()) => {
            event!(Level::INFO, "Sucessfully saved MIDI file '{}'", midi_filepath.to_string_lossy());
        }
        Err(e) => {
            rfd::MessageDialog::new()
                .set_level(rfd::MessageLevel::Error)
                .set_title("Unable to save MIDI file")
                .set_description(&e.to_string())
                .show();
            event!(Level::ERROR, "error writing MIDI file: {:?}", e);
        }
    };
}
fn open(monodrone_ctx : *mut lean_sys::lean_object, track : &UITrack, cur_filepath : &mut AppFilePath) -> *mut lean_sys::lean_object {
    let open_dialog = FileDialog::new()
        .add_filter("monodrone", &["drn"])
        .set_can_create_directories(true)
        .set_title("Open monodrone file location")
        .set_directory(cur_filepath.parent_dir());

    if let Some(path) = open_dialog.pick_file() {
        // open path and load string.
        event!(Level::INFO, "loading file {cur_filepath:?}");
        match File::open(path.clone()) {
            Ok(file) => {
                let reader = std::io::BufReader::new(file);
                let str = std::io::read_to_string(reader).unwrap();
                event!(Level::INFO, "loaded file data: {str}");
                let monodrone_ctx = match monodroneffi::ctx_from_json_str(str) {
                    Ok(new_ctx) => {
                        cur_filepath.set_file_path(&path);
                        new_ctx
                    }

                    Err(e) => {
                        rfd::MessageDialog::new()
                            .set_level(rfd::MessageLevel::Error)
                            .set_title("Unable to load file, JSON parsing error.")
                            .set_description(&e)
                            .show();
                        event!(Level::ERROR, "error loading file: {:?}", e);
                        monodrone_ctx
                    }
                };
                event!(Level::INFO, "loaded file!");
                monodrone_ctx
            }
            Err(e) => {
                event!(Level::ERROR, "error opening file: {:?}", e);
                monodrone_ctx
            }
        }
    }
    else {
        monodrone_ctx
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
    // let SCREEN_WIDTH = unsafe { GetScreenWidth() };
    // let SCREEN_HEIGHT = unsafe { GetScreenHeight() };

    let SCREEN_WIDTH = 800;
    let SCREEN_HEIGHT = 600;
    let options = eframe::NativeOptions {
        viewport: egui::ViewportBuilder::default().with_inner_size([SCREEN_WIDTH as f32, SCREEN_HEIGHT as f32]),
        ..Default::default()
    };

    // rl.set_window_size(rl.get_screen_width(), rl.get_screen_height());

    // unsafe {
    //     let file_data = include_bytes!("../favicon.ico");
    //     let filetype = "ico";
    //     let ico = raylib::ffi::LoadImageFromMemory(
    //         filetype.as_ptr() as *const i8,
    //         file_data.as_ptr() as *const u8,
    //         file_data.len() as i32,
    //     );
    //     raylib::ffi::SetWindowIcon(ico);
    // };

    let TARGET_FPS = 60;

    event!(Level::INFO, "creating context");
    let mut cur_filepath = AppFilePath::new_whimsical();
    event!(
        Level::INFO,
        "initial file path: {:?} | dir: {:?} | basename: {:?}",
        cur_filepath,
        cur_filepath.parent_dir(),
        cur_filepath.file_stem()
    );

    let mut monodrone_ctx = monodroneffi::new_context(&cur_filepath.to_string());

    let mut track = monodroneffi::UITrack::from_lean(monodrone_ctx);
    event!(Level::INFO, "track: {:?}", track);
    let mut selection = monodroneffi::Selection::from_lean(monodrone_ctx);
    event!(Level::INFO, "selection: {:?}", selection);

    let mut debounceMovement = Debouncer::new(80.0 / 1000.0);
    let mut debounceUndo = Debouncer::new(150.0 / 1000.0);

    let mut cameraYEaser = Easer::new(0.0);
    let mut nowPlayingYEaser = Easer::new(0.0);
    let mut cursorEaser = Easer2d::new(0.0, 0.0);
    let mut selectAnchorEaser = Easer2d::new(0.0, 0.0);

    let mut sequencerPlaybackSpeed = SequenceNumbered::new(1.0 as f64);
    nowPlayingYEaser.damping = 0.4;

    let mut tweak : u8 =100;
    let mut filename : String = "untitled".to_string();
    let mut show_metadata : bool = false;
    let _ = eframe::run_simple_native(format!("monodrone({})", cur_filepath.to_string()).as_str(),
        options, move |ctx, _frame| {
        egui::TopBottomPanel::bottom("Configuration").exact_height(egui::style::Spacing::default().interact_size.y).show(ctx, |ui| {
            ui.add(egui::Slider::new(&mut sequencerPlaybackSpeed.value, 0.0..=100.0).text("Playback Speed"));
            // ui.add(egui::TextEdit::singleline(&mut filename));
            // ui.label(format!("Playback Speed: {:1}", sequencerPlaybackSpeed.value));
            // let text = format!("Playback Speed: {:.1}", sequencerPlaybackSpeed.value);
            // let text_galley = painter.layout_no_wrap(text,
            // FontId::monospace(15.),
            // PLAYBACK_SPEED_TEXT_COLOR);
            // painter.galley(Pos2::new(SCREEN_WIDTH as f32 - text_galley.rect.width() - 20.0 , text_galley.rect.height() + 5.0),
            //     text_galley, PLAYBACK_SPEED_TEXT_COLOR);

        });

        egui::TopBottomPanel::top("top bar").show(ctx, |ui| {
            egui::menu::bar(ui, |ui| {
                if ui.button("Open").clicked() {
                    monodrone_ctx = open(monodrone_ctx, &track, &mut cur_filepath);
                }
                if ui.button("Save").clicked() {
                    save(monodrone_ctx, &track, &cur_filepath);
                }
                if ui.button("Save As").clicked() {
                    panic!("TODO: port save as implementation.")
                }
                if ui.button("Metadata").clicked() {
                    show_metadata = true;
                }
            });
        });
        egui::CentralPanel::default().show(ctx, |ui| {
            // return;
            // let time_elapsed = rl.get_frame_time();
            let time_elapsed = 0.01; // TODO: fix this!
            debounceMovement.add_time_elapsed(time_elapsed);
            debounceUndo.add_time_elapsed(time_elapsed);

            // Step 2: Get stuff to render
            if monodroneffi::get_track_sync_index(monodrone_ctx) != track.sync_index {
                track = monodroneffi::UITrack::from_lean(monodrone_ctx);
                save(monodrone_ctx, &track, &cur_filepath);
                println!("-> got new track {:?}", track);

            }

            // for this particular case, the pattern doesn't make much sense.
            // Still, it's nice to establish a pattern for future use.
            if sequencerPlaybackSpeed.update_seq(monodroneffi::get_playback_speed_sequence_number(
                monodrone_ctx,
            )) {
                let new_speed = monodroneffi::get_playback_speed(monodrone_ctx);
                sequencerPlaybackSpeed.set_value(new_speed);
                sequencer_io.set_playback_rate(new_speed as f32);
                event!(Level::INFO, "new playback speed: {:?}", sequencerPlaybackSpeed);
            }
            if monodroneffi::get_cursor_sync_index(monodrone_ctx) != selection.sync_index {
                selection = monodroneffi::Selection::from_lean(monodrone_ctx);
                event!(Level::INFO, "new selection {:?}", selection);
            }


            if ctx.input(|i| i.key_pressed(Key::C)) {
                monodrone_ctx = monodroneffi::set_pitch(monodrone_ctx, monodroneffi::PitchName::C);
            }
            if ctx.input(|i| i.key_pressed(Key::D)) {
                monodrone_ctx = monodroneffi::set_pitch(monodrone_ctx, monodroneffi::PitchName::D);
            }
            if ctx.input(|i| i.key_pressed(Key::E)) {
                monodrone_ctx = monodroneffi::set_pitch(monodrone_ctx, monodroneffi::PitchName::E);
            }
            if ctx.input(|i| i.key_pressed(Key::F)) {
                monodrone_ctx = monodroneffi::set_pitch(monodrone_ctx, monodroneffi::PitchName::F);
            }
            if ctx.input(|i| i.key_pressed(Key::G)) {
                monodrone_ctx = monodroneffi::set_pitch(monodrone_ctx, monodroneffi::PitchName::G);
            }
            if ctx.input(|i| i.key_pressed(Key::A)) {
                monodrone_ctx = monodroneffi::set_pitch(monodrone_ctx, monodroneffi::PitchName::A);
            }
            if ctx.input(|i| i.key_pressed(Key::B)) {
                monodrone_ctx = monodroneffi::set_pitch(monodrone_ctx, monodroneffi::PitchName::B);
            }
            if ctx.input(|i| i.key_pressed(Key::Space)) {
                if sequencer_io.is_playing() {
                    sequencer_io.stop();
                } else {
                    sequencer_io.set_track(track.clone().to_player_track());
                    let end_instant = track.get_last_instant() as u64;
                    let start_instant = 0;
                    let is_looping = false;
                    sequencer_io.restart(start_instant, (end_instant + 1), is_looping);
                }
            }


            if ctx.input(|i| i.key_pressed(Key::H)) {
                monodrone_ctx = monodroneffi::cursor_move_left_one(monodrone_ctx)
            }
            if ctx.input(|i| i.key_pressed(Key::J)) {
                if ctx.input(|i| i.modifiers.shift) {
                    monodrone_ctx = monodroneffi::lower_octave(monodrone_ctx);
                }
                else if ctx.input(|i| i.modifiers.command) {
                    monodrone_ctx = monodroneffi::increase_nsteps(monodrone_ctx);
                }
                else {
                    monodrone_ctx = monodroneffi::cursor_move_down_one(monodrone_ctx);
                }
            }
            if ctx.input(|i| i.key_pressed(Key::K)) {
                if ctx.input(|i| i.modifiers.shift) {
                    monodrone_ctx = monodroneffi::raise_octave(monodrone_ctx);
                }
                else if ctx.input(|i| i.modifiers.command) {
                    monodrone_ctx = monodroneffi::decrease_nsteps(monodrone_ctx);
                }
                else {
                    monodrone_ctx = monodroneffi::cursor_move_up_one(monodrone_ctx)
                }
            }
            if ctx.input(|i| i.key_pressed(Key::L)) {
                monodrone_ctx = monodroneffi::cursor_move_right_one(monodrone_ctx);
            }
            if ctx.input(|i| i.key_pressed(Key::Backspace)) {
                if ctx.input(|i| i.modifiers.shift) {
                    monodrone_ctx = monodroneffi::delete_line(monodrone_ctx);
                } else {
                    monodrone_ctx = monodroneffi::delete_note(monodrone_ctx);
                }
            }
            if ctx.input(|i| i.key_pressed(Key::S) && i.modifiers.command) {
                save(monodrone_ctx, &track, &cur_filepath);
            }
            if ctx.input(|i| i.key_pressed(Key::O) && i.modifiers.command) {
                monodrone_ctx = open(monodrone_ctx, &track, &mut cur_filepath);
            }

            if ctx.input(|i| i.key_pressed(Key::Z) && i.modifiers.command) {
                if ctx.input(|i| i.modifiers.shift) {
                    monodrone_ctx = monodroneffi::redo_action(monodrone_ctx);
                } else {
                    monodrone_ctx = monodroneffi::undo_action(monodrone_ctx);
                }
            }
            if ctx.input (|i| i.key_pressed(Key::Num2)) {
                monodrone_ctx = monodroneffi::toggle_flat(monodrone_ctx);
            }
            if ctx.input (|i| i.key_pressed(Key::Num3)) {
                monodrone_ctx = monodroneffi::toggle_sharp(monodrone_ctx);
            }

            // let (response, painter) = ui.allocate_painter(size, Sense::hover());
            let painter = ui.painter_at(ui.available_rect_before_wrap());
            let child_rect = ui.available_rect_before_wrap(); // TODO: Refactor code to use this rect.

            let START_Y : f32 = ui.min_rect().top();
            let BOX_HEIGHT = 40.;
            let BOX_WIDTH = 40.;
            let BOX_WIDTH_PADDING_LEFT = 5.;
            let BOX_WINDOW_CORNER_PADDING_LEFT = BOX_WIDTH_PADDING_LEFT;
            let BOX_WIDTH_PADDING_RIGHT = 5.;
            let BOX_HEIGHT_PADDING_TOP = 5.;
            let BOX_WINDOW_CORNER_PADDING_TOP : f32 = BOX_HEIGHT_PADDING_TOP;

            let BOX_HEIGHT_PADDING_BOTTOM = 5.;
            let BOX_DESLECTED_COLOR = egui::Color32::from_rgb(66, 66, 66);
            let BOX_SELECTED_BACKGROUND_COLOR = egui::Color32::from_rgb(255, 0, 100);
            let BOX_CURSORED_COLOR = egui::Color32::from_rgb(99, 99, 99);
            let BOX_NOW_PLAYING_COLOR = egui::Color32::from_rgb(255, 143, 0);
            let TEXT_COLOR_LEADING = egui::Color32::from_rgb(207, 216, 220);
            let TEXT_COLOR_FOLLOWING = egui::Color32::from_rgb(99, 99, 99);
            let PLAYBACK_SPEED_TEXT_COLOR = egui::Color32::from_rgb(97, 97, 97);

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

            // now playing.
            {
                let cur_instant = sequencer_io.sequencer.lock().as_ref().unwrap().cur_instant;
                let now_playing_box_y : i32 = (cur_instant as i32 - 1); // keep this an int so tweenig looks cool.

                nowPlayingYEaser.set(
                    (BOX_WINDOW_CORNER_PADDING_TOP
                        + now_playing_box_y as f32
                            * (BOX_HEIGHT + BOX_HEIGHT_PADDING_TOP + BOX_HEIGHT_PADDING_BOTTOM))
                        as f32,
                );
                nowPlayingYEaser.step(time_elapsed);
            }

            let logical_x_to_draw_x = |ix: f32| -> f32 {
                BOX_WINDOW_CORNER_PADDING_LEFT
                    + (ix * (BOX_WIDTH + BOX_WIDTH_PADDING_LEFT + BOX_WIDTH_PADDING_RIGHT) as f32)
                    + BOX_WIDTH_PADDING_LEFT
            };

            let logical_y_to_draw_y = |iy: f32| -> f32 {
                BOX_WINDOW_CORNER_PADDING_TOP
                    + (iy * (BOX_HEIGHT + BOX_HEIGHT_PADDING_TOP + BOX_HEIGHT_PADDING_BOTTOM) as f32)
                    + BOX_HEIGHT_PADDING_TOP
                    - cameraYEaser.get()
            };

            let logical_width_to_draw_width = |width: f32| -> f32 {
                (width * (BOX_WIDTH) as f32
                    + (width - 1.0) * (BOX_WIDTH_PADDING_LEFT as f32 + BOX_WIDTH_PADDING_RIGHT as f32))
            };

            let logical_height_to_draw_height = |height: f32| -> f32 {
                (height * (BOX_HEIGHT) as f32
                    + (height - 1.0)
                        * (BOX_HEIGHT_PADDING_TOP as f32 + BOX_HEIGHT_PADDING_BOTTOM as f32))
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
                    let draw_x = logical_x_to_draw_x(x  as f32);
                    let draw_y = logical_y_to_draw_y(y  as f32);
                    painter.rect_filled (Rect::from_min_size(Pos2::new(draw_x, draw_y),
                        Vec2::new(BOX_WIDTH, BOX_HEIGHT)),
                        egui::Rounding::default().at_least(4.0),
                        BOX_DESLECTED_COLOR);
                }
            }

            painter.rect_filled (Rect::from_min_size(Pos2::new(cursor_draw_x, cursor_draw_y),
                Vec2::new(BOX_WIDTH * 0.2 , BOX_HEIGHT)),
                Rounding::default(),
                BOX_CURSORED_COLOR);

            for x in 0u64..8 {
                for y in 0u64..100 {
                    let draw_x = logical_x_to_draw_x(x as f32);
                    let draw_y = logical_y_to_draw_y(y as f32);

                    match track.get_note_from_coord(x, y) {
                        Some(note) => {
                            let text_color = if (note.x == x && note.y == y) {
                                TEXT_COLOR_LEADING
                            } else {
                                TEXT_COLOR_FOLLOWING
                            };

                            painter.text(Pos2::new(draw_x + 5., draw_y + 5.),
                                Align2::LEFT_TOP,
                                note.to_str(),
                                FontId::monospace(20.),
                                text_color);

                            let OCTAVE_TEXT_PADDING = 2;
                            let octave_text_color = egui::Color32::from_rgb(104, 159, 56);
                            let octave_text = painter.layout_no_wrap(note.octave.to_string(),
                                FontId::monospace(15.),
                                octave_text_color);
                            let text_pos =
                                Pos2::new(draw_x + BOX_WIDTH - octave_text.rect.width() - OCTAVE_TEXT_PADDING as f32,
                                    draw_y + BOX_HEIGHT - octave_text.rect.height() - OCTAVE_TEXT_PADDING as f32);

                            painter.galley(text_pos, octave_text, octave_text_color);
                        }
                        None => (),
                    };
                }
            }

            // print!("camera y easer: {}", cameraYEaser.get());
            // TODO: I have no clue where these weird constants come from!
            painter.rect_filled (Rect::from_min_size(
                Pos2::new(10., 5.0 + nowPlayingYEaser.get() - cameraYEaser.get()),
                Vec2::new(BOX_WIDTH * 0.1, BOX_HEIGHT)),
                Rounding::default().at_least(4.0),
                BOX_NOW_PLAYING_COLOR);
            ctx.request_repaint();
        });

        egui::Window::new("Edit MIDI metadata").open(&mut show_metadata).show(ctx, |ui| {
            // time signature.
            // author.
            // egui::widgets::TextEdit::singleline("Author")

         });

    });

    // while !rl.window_should_close() {
    //     let time_elapsed = rl.get_frame_time();
    //     debounceMovement.add_time_elapsed(time_elapsed);
    //     debounceUndo.add_time_elapsed(time_elapsed);

    //     // Step 2: Get stuff to render
    //     if monodroneffi::get_track_sync_index(monodrone_ctx) != track.sync_index {
    //         track = monodroneffi::UITrack::from_lean(monodrone_ctx);
    //         // TODO: bundle all this state update in a single place.
    //         println!("-> got new track {:?}", track);
    //     }

    //     // for this particular case, the pattern doesn't make much sense.
    //     // Still, it's nice to establish a pattern for future use.
    //     if sequencerPlaybackSpeed.update_seq(monodroneffi::get_playback_speed_sequence_number(
    //         monodrone_ctx,
    //     )) {
    //         let new_speed = monodroneffi::get_playback_speed(monodrone_ctx);
    //         sequencerPlaybackSpeed.set_value(new_speed);
    //         sequencer_io.set_playback_rate(new_speed as f32);
    //         print!("-> got new playback speed: {:?}", sequencerPlaybackSpeed);
    //     }
    //     if monodroneffi::get_cursor_sync_index(monodrone_ctx) != selection.sync_index {
    //         selection = monodroneffi::Selection::from_lean(monodrone_ctx);
    //         println!("-> got new selection");
    //     }
    //     if rl.is_key_pressed(KeyboardKey::KEY_MINUS) {
    //         monodrone_ctx = monodroneffi::decrease_playback_speed(monodrone_ctx);
    //     } else if rl.is_key_pressed(KeyboardKey::KEY_EQUAL) {
    //         monodrone_ctx = monodroneffi::increase_playback_speed(monodrone_ctx);
    //     } else if rl.is_key_pressed(KeyboardKey::KEY_SPACE) {
    //         if sequencer_io.is_playing() {
    //             sequencer_io.stop();
    //         } else {
    //             sequencer_io.set_track(track.clone().to_player_track());
    //             let is_looping = is_shift_key_down(&rl);

    //             let start_instant = if is_looping {
    //                 cmp::min(
    //                     cmp::min(selection.cursor_y, selection.anchor_y) as u64,
    //                     track.get_last_instant() as u64,
    //                 )
    //             } else {
    //                 if is_shift_key_down(&rl) {
    //                     selection.cursor_y as u64
    //                 } else {
    //                     0
    //                 }
    //             };

    //             let end_instant = if is_looping {
    //                 cmp::max(
    //                     cmp::max(selection.cursor_y, selection.anchor_y) as u64,
    //                     track.get_last_instant() as u64,
    //                 )
    //             } else {
    //                 track.get_last_instant() as u64
    //             };
    //             sequencer_io.restart(start_instant, (end_instant + 1), is_looping);
    //         }
    //     } else if (debounceMovement.debounce(rl.is_key_down(KeyboardKey::KEY_J))) {
    //         if is_shift_key_down(&rl) {
    //             monodrone_ctx = monodroneffi::set_nsteps(monodrone_ctx, 2);
    //             // monodrone_ctx = monodroneffi::drag_down_one(monodrone_ctx);
    //             // panic!("monodrone ctx drag down one");
    //         } else {
    //             monodrone_ctx = monodroneffi::cursor_move_down_one(monodrone_ctx);
    //         }
    //     } else if (debounceMovement.debounce(rl.is_key_down(KeyboardKey::KEY_K))) {
    //         if is_shift_key_down(&rl) {
    //             monodrone_ctx = monodroneffi::set_nsteps(monodrone_ctx, 3);
    //             // monodrone_ctx = monodroneffi::drag_up_one(monodrone_ctx);
    //         } else {
    //             monodrone_ctx = monodroneffi::cursor_move_up_one(monodrone_ctx);
    //         }
    //     } else if (debounceMovement.debounce(rl.is_key_down(KeyboardKey::KEY_H))) {
    //         if (is_shift_key_down(&rl)) {
    //             monodrone_ctx = monodroneffi::set_nsteps(monodrone_ctx, 1);
    //         } else {
    //             monodrone_ctx = monodroneffi::cursor_move_left_one(monodrone_ctx);
    //         }
    //     } else if (debounceMovement.debounce(rl.is_key_down(KeyboardKey::KEY_L))) {
    //         if (is_shift_key_down(&rl)) {
    //             monodrone_ctx = monodroneffi::set_nsteps(monodrone_ctx, 4);
    //         } else {
    //             monodrone_ctx = monodroneffi::cursor_move_right_one(monodrone_ctx);
    //         }
    //     } else if rl.is_key_pressed(KeyboardKey::KEY_Q) {
    //         monodrone_ctx = monodroneffi::decrease_nsteps(monodrone_ctx);
    //     } else if rl.is_key_pressed(KeyboardKey::KEY_W) {
    //         monodrone_ctx = monodroneffi::increase_nsteps(monodrone_ctx);
    //     } else if (rl.is_key_pressed(KeyboardKey::KEY_C)) {
    //         monodrone_ctx = monodroneffi::set_pitch(monodrone_ctx, monodroneffi::PitchName::C);
    //     } else if (rl.is_key_pressed(KeyboardKey::KEY_D)) {
    //         monodrone_ctx = monodroneffi::set_pitch(monodrone_ctx, monodroneffi::PitchName::D);
    //     } else if (rl.is_key_pressed(KeyboardKey::KEY_E)) {
    //         monodrone_ctx = monodroneffi::set_pitch(monodrone_ctx, monodroneffi::PitchName::E);
    //     } else if (rl.is_key_pressed(KeyboardKey::KEY_F)) {
    //         monodrone_ctx = monodroneffi::set_pitch(monodrone_ctx, monodroneffi::PitchName::F);
    //     } else if (rl.is_key_pressed(KeyboardKey::KEY_G)) {
    //         monodrone_ctx = monodroneffi::set_pitch(monodrone_ctx, monodroneffi::PitchName::G);
    //     } else if (rl.is_key_pressed(KeyboardKey::KEY_A)) {
    //         monodrone_ctx = monodroneffi::set_pitch(monodrone_ctx, monodroneffi::PitchName::A);
    //     } else if (rl.is_key_pressed(KeyboardKey::KEY_B)) {
    //         monodrone_ctx = monodroneffi::set_pitch(monodrone_ctx, monodroneffi::PitchName::B);
    //     } else if (debounceMovement.debounce(rl.is_key_down(KeyboardKey::KEY_BACKSPACE))) {
    //         if (is_shift_key_down(&rl)) {
    //             monodrone_ctx = monodroneffi::delete_line(monodrone_ctx);
    //         } else {
    //             monodrone_ctx = monodroneffi::delete_note(monodrone_ctx);
    //         }
    //     } else if (debounceUndo.debounce(rl.is_key_down(KeyboardKey::KEY_Z))) {
    //         // TODO: figure out how to get control key.
    //         if (is_shift_key_down(&rl)) {
    //             monodrone_ctx = monodroneffi::redo_action(monodrone_ctx);
    //         } else {
    //             monodrone_ctx = monodroneffi::undo_action(monodrone_ctx);
    //         }
    //     } else if (rl.is_key_pressed(KeyboardKey::KEY_THREE)) {
    //         monodrone_ctx = monodroneffi::toggle_sharp(monodrone_ctx);
    //     } else if rl.is_key_pressed(KeyboardKey::KEY_TWO) {
    //         monodrone_ctx = monodroneffi::toggle_flat(monodrone_ctx);
    //     } else if (rl.is_key_pressed(KeyboardKey::KEY_COMMA)) {
    //         monodrone_ctx = monodroneffi::lower_octave(monodrone_ctx);
    //     } else if (rl.is_key_pressed(KeyboardKey::KEY_PERIOD)) {
    //         monodrone_ctx = monodroneffi::raise_octave(monodrone_ctx);
    //     } else if debounceMovement.debounce(rl.is_key_down(KeyboardKey::KEY_ENTER)) {
    //         monodrone_ctx = monodroneffi::newline(monodrone_ctx);
    //         monodrone_ctx = monodroneffi::cursor_move_down_one(monodrone_ctx);
    //     } else if (!is_shift_key_down(&rl)
    //         && rl.is_key_pressed(KeyboardKey::KEY_S)
    //         && is_control_key_down(&rl))
    //     {
    //         // c-s for save.
    //         let str = monodroneffi::ctx_to_json_str(monodrone_ctx);
    //         event!(Level::INFO, "saving file to path: '{}'", cur_filepath.to_string());
    //         match File::create(cur_filepath.path.as_path()) {
    //             Ok(mut file) => {
    //                 file.write_all(str.as_bytes()).unwrap();
    //                 event!(Level::INFO, "Successfully saved '{}'", cur_filepath.to_string());

    //             }
    //             Err(e) => {
    //                 event!(Level::ERROR, "Error saving file: {:?}", e);
    //                 rfd::MessageDialog::new()
    //                     .set_level(rfd::MessageLevel::Error)
    //                     .set_title(format!(
    //                         "Unable to save file to path '{}'.",
    //                         cur_filepath.to_string()
    //                     ))
    //                     .set_description(e.to_string())
    //                     .show();
    //             }
    //         };
    //         let midi_filepath = cur_filepath.get_export_file_path();
    //         let midi_file = match File::create(midi_filepath.clone()) {
    //             Ok(file) => file,
    //             Err(e) => {
    //                 rfd::MessageDialog::new()
    //                     .set_level(rfd::MessageLevel::Error)
    //                     .set_title("Unable to create MIDI file")
    //                     .set_description(e.to_string())
    //                     .show();
    //                 event!(Level::ERROR, "error creating MIDI file: {:?}", e);
    //                 return;
    //             }
    //         };
    //         let player_track = track.to_player_track();
    //         let (header, tracks) = player_track.to_smf();
    //         match midly::write_std(&header, tracks.iter(), midi_file) {
    //             Ok(()) => {
    //                 event!(Level::INFO, "Sucessfully saved MIDI file '{}'", midi_filepath.to_string_lossy());
    //             }
    //             Err(e) => {
    //                 rfd::MessageDialog::new()
    //                     .set_level(rfd::MessageLevel::Error)
    //                     .set_title("Unable to save MIDI file")
    //                     .set_description(&e.to_string())
    //                     .show();
    //                 event!(Level::ERROR, "error writing MIDI file: {:?}", e);
    //             }
    //         }

    //     } else if is_shift_key_down(&rl)
    //         && rl.is_key_pressed(KeyboardKey::KEY_E)
    //         && is_control_key_down(&rl) {
    //         // TODO: export to MIDI.
    //     } else if is_shift_key_down(&rl)
    //         && rl.is_key_pressed(KeyboardKey::KEY_I)
    //         && is_control_key_down(&rl) {
    //         // TODO: import MIDI to monodrone.
    //     } else if is_shift_key_down(&rl)
    //         && rl.is_key_pressed(KeyboardKey::KEY_S)
    //         && is_control_key_down(&rl)
    //     {
    //         // TODO: only open this with ctrl + shift + s.
    //         let saver_dialog = FileDialog::new()
    //             .add_filter("monodrone", &["drn"])
    //             .set_can_create_directories(true)
    //             .set_file_name(cur_filepath.file_stem().to_string_lossy())
    //             .set_directory(cur_filepath.parent_dir())
    //             .set_title("Save monodrone file location");

    //         if let Option::Some(path) = saver_dialog.save_file() {
    //             let str = monodroneffi::ctx_to_json_str(monodrone_ctx);
    //             // open file and write string.
    //             event!(Level::INFO, "saving-as file to path {path:?}");
    //             match File::create(path.clone()) {
    //                 Ok(mut file) => {
    //                     file.write_all(str.as_bytes()).unwrap();
    //                     cur_filepath.set_file_path(&rl, &thread, &path);
    //                 }
    //                 Err(e) => {
    //                     rfd::MessageDialog::new()
    //                         .set_level(rfd::MessageLevel::Error)
    //                         .set_title("Unable to save monodrone file")
    //                         .set_description(&e.to_string())
    //                         .show();
    //                     event!(Level::ERROR, "error saving monodrone file: {:?}", e);
    //                 }
    //             };

    //             let midi_filepath = cur_filepath.get_export_file_path();
    //             let midi_file = match File::create(midi_filepath.clone()) {
    //                 Ok(file) => file,
    //                 Err(e) => {
    //                     rfd::MessageDialog::new()
    //                         .set_level(rfd::MessageLevel::Error)
    //                         .set_title("Unable to create MIDI file")
    //                         .set_description(&e.to_string())
    //                         .show();
    //                     event!(Level::ERROR, "error creating MIDI file: {:?}", e);
    //                     return;
    //                 }
    //             };
    //             let player_track = track.to_player_track();
    //             let (header, tracks) = player_track.to_smf();
    //             match midly::write_std(&header, tracks.iter(), midi_file) {
    //                 Ok(()) => {
    //                     event!(Level::INFO, "Sucessfully saved MIDI file '{}'", midi_filepath.to_string_lossy());
    //                 }
    //                 Err(e) => {
    //                     rfd::MessageDialog::new()
    //                         .set_level(rfd::MessageLevel::Error)
    //                         .set_title("Unable to save MIDI file")
    //                         .set_description(&e.to_string())
    //                         .show();
    //                     event!(Level::ERROR, "error writing MIDI file: {:?}", e);
    //                 }
    //             }
    //         } else {
    //             event!(Level::INFO, "no path selected for save");
    //         }
    //     } else if rl.is_key_pressed(KeyboardKey::KEY_O) && is_control_key_down(&rl) {
    //         let open_dialog = FileDialog::new()
    //             .add_filter("monodrone", &["drn"])
    //             .set_can_create_directories(true)
    //             .set_title("Open monodrone file location")
    //             .set_directory(cur_filepath.parent_dir());

    //         if let Some(path) = open_dialog.pick_file() {
    //             // open path and load string.
    //             event!(Level::INFO, "loading file {cur_filepath:?}");
    //             match File::open(path.clone()) {
    //                 Ok(file) => {
    //                     let reader = std::io::BufReader::new(file);
    //                     let str = std::io::read_to_string(reader).unwrap();
    //                     event!(Level::INFO, "loaded file data: {str}");
    //                     monodrone_ctx = match monodroneffi::ctx_from_json_str(str) {
    //                         Ok(new_ctx) => {
    //                             cur_filepath.set_file_path(&rl, &thread, &path);
    //                             new_ctx
    //                         }

    //                         Err(e) => {
    //                             rfd::MessageDialog::new()
    //                                 .set_level(rfd::MessageLevel::Error)
    //                                 .set_title("Unable to load file, JSON parsing error.")
    //                                 .set_description(&e)
    //                                 .show();
    //                             event!(Level::ERROR, "error loading file: {:?}", e);
    //                             monodrone_ctx
    //                         }
    //                     };
    //                     track = monodroneffi::UITrack::from_lean(monodrone_ctx);
    //                     selection = monodroneffi::Selection::from_lean(monodrone_ctx);
    //                     event!(Level::INFO, "loaded file!");
    //                 }
    //                 Err(e) => {
    //                     event!(Level::ERROR, "error opening file: {:?}", e);
    //                 }
    //             }
    //         } else {
    //             event!(Level::INFO, "no path selected for open");
    //         }
    //     } else if rl.is_key_pressed(KeyboardKey::KEY_Q) && is_control_key_down(&rl) {
    //         break;
    //     }

    //     // Step 3: Render
    //     let mut d = rl.begin_drawing(&thread);

    //     d.clear_background(Color::new(33, 33, 33, 255));
    //     // d.clear_background(Color::new(38, 50, 56, 255));
    //     let BOX_HEIGHT = 40;
    //     let BOX_WIDTH = 40;
    //     let BOX_WIDTH_PADDING_LEFT = 5;
    //     let BOX_WINDOW_CORNER_PADDING_LEFT = BOX_WIDTH_PADDING_LEFT;
    //     let BOX_WIDTH_PADDING_RIGHT = 5;
    //     let BOX_HEIGHT_PADDING_TOP = 5;
    //     let BOX_WINDOW_CORNER_PADDING_TOP = BOX_HEIGHT_PADDING_TOP;
    //     let BOX_NOW_PLAYING_SUGAR_WIDTH = 5;

    //     let BOX_HEIGHT_PADDING_BOTTOM = 5;
    //     let BOX_DESLECTED_COLOR = Color::new(66, 66, 66, 255);
    //     let BOX_SELECTED_BACKGROUND_COLOR = Color::new(255, 0, 100, 255);
    //     let BOX_CURSORED_COLOR = Color::new(99, 99, 99, 255);
    //     let BOX_NOW_PLAYING_COLOR = Color::new(255, 143, 0, 255);
    //     let TEXT_COLOR_LEADING = Color::new(207, 216, 220, 255);
    //     let TEXT_COLOR_FOLLOWING = Color::new(99, 99, 99, 255);
    //     let PLAYBACK_SPEED_TEXT_COLOR = Color::new(97, 97, 97, 255);

    //     let PLAYBACK_SPEED_INFO_Y = BOX_WINDOW_CORNER_PADDING_TOP;

    //     cameraYEaser.set(
    //         ((selection.anchor_y as f32
    //             * (BOX_HEIGHT + BOX_HEIGHT_PADDING_TOP + BOX_HEIGHT_PADDING_BOTTOM) as f32)
    //             - SCREEN_HEIGHT as f32 * 0.5)
    //             .max(0.0),
    //     );
    //     cameraYEaser.step(time_elapsed);

    //     cursorEaser.set(selection.cursor_x as f32, selection.cursor_y as f32);
    //     cursorEaser.damping = 0.3;
    //     cursorEaser.step(time_elapsed);

    //     selectAnchorEaser.set(selection.anchor_x as f32, selection.anchor_y as f32);
    //     selectAnchorEaser.damping = 0.2;
    //     selectAnchorEaser.step(time_elapsed);

    //     // draw tracker.
    //     {
    //         let cur_instant = sequencer_io.sequencer.lock().as_ref().unwrap().cur_instant;
    //         let now_playing_box_y = ((cur_instant as i32 - 1) as i32);

    //         nowPlayingYEaser.set(
    //             (BOX_WINDOW_CORNER_PADDING_TOP
    //                 + now_playing_box_y
    //                     * (BOX_HEIGHT + BOX_HEIGHT_PADDING_TOP + BOX_HEIGHT_PADDING_BOTTOM))
    //                 as f32,
    //         );
    //         nowPlayingYEaser.step(time_elapsed);
    //     }

    //     let logical_x_to_draw_x = |ix: f32| -> i32 {
    //         BOX_WINDOW_CORNER_PADDING_LEFT
    //             + (ix * (BOX_WIDTH + BOX_WIDTH_PADDING_LEFT + BOX_WIDTH_PADDING_RIGHT) as f32)
    //                 as i32
    //             + BOX_WIDTH_PADDING_LEFT
    //     };

    //     let logical_y_to_draw_y = |iy: f32| -> i32 {
    //         BOX_WINDOW_CORNER_PADDING_TOP
    //             + (iy * (BOX_HEIGHT + BOX_HEIGHT_PADDING_TOP + BOX_HEIGHT_PADDING_BOTTOM) as f32)
    //                 as i32
    //             + BOX_HEIGHT_PADDING_TOP
    //             - cameraYEaser.get() as i32
    //     };

    //     let logical_width_to_draw_width = |width: f32| -> i32 {
    //         (width * (BOX_WIDTH) as f32
    //             + (width - 1.0) * (BOX_WIDTH_PADDING_LEFT as f32 + BOX_WIDTH_PADDING_RIGHT as f32))
    //             as i32
    //     };

    //     let logical_height_to_draw_height = |height: f32| -> i32 {
    //         (height * (BOX_HEIGHT) as f32
    //             + (height - 1.0)
    //                 * (BOX_HEIGHT_PADDING_TOP as f32 + BOX_HEIGHT_PADDING_BOTTOM as f32))
    //             as i32
    //     };

    //     let cursor_draw_x = logical_x_to_draw_x(cursorEaser.get().0);
    //     let cursor_draw_y = logical_y_to_draw_y(cursorEaser.get().1);

    //     let select_anchor_draw_x = logical_x_to_draw_x(selectAnchorEaser.get().0);
    //     let select_anchor_draw_y = logical_y_to_draw_y(selectAnchorEaser.get().1);

    //     let top_left_draw_x = cursor_draw_x.min(select_anchor_draw_x);
    //     let top_left_draw_y = cursor_draw_y.min(select_anchor_draw_y);
    //     let bottom_right_draw_x = cursor_draw_x.max(select_anchor_draw_x);
    //     let bottom_right_draw_y = cursor_draw_y.max(select_anchor_draw_y);

    //     // if selection.cursor_x != selection.anchor_x || selection.cursor_y != selection.anchor_y {
    //     //     d.draw_rectangle(
    //     //         top_left_draw_x as i32,
    //     //         top_left_draw_y as i32,
    //     //         logical_width_to_draw_width((cursorEaser.get().0 - selectAnchorEaser.get().0).abs() + 1.0) as i32,
    //     //         logical_height_to_draw_height((cursorEaser.get().1 - selectAnchorEaser.get().1).abs() + 1.0) as i32,
    //     //         BOX_SELECTED_BACKGROUND_COLOR,
    //     //     );
    //     // }

    //     for x in 0u64..8 {
    //         for y in 0u64..100 {
    //             let draw_x = logical_x_to_draw_x(x as f32);
    //             let draw_y = logical_y_to_draw_y(y as f32);
    //             let draw_color = if x == selection.cursor_x && y == selection.cursor_y {
    //                 // BOX_SELECTED_BACKGROUND_COLOR
    //                 BOX_DESLECTED_COLOR
    //             } else if top_left_draw_x <= draw_x
    //                 && (draw_x - bottom_right_draw_x) <= BOX_WIDTH / 5
    //                 && top_left_draw_y <= draw_y
    //                 && (draw_y - bottom_right_draw_y) <= BOX_HEIGHT / 5
    //             {
    //                 BOX_DESLECTED_COLOR
    //             } else {
    //                 BOX_DESLECTED_COLOR
    //             };

    //             d.draw_rectangle(
    //                 draw_x as i32,
    //                 draw_y as i32,
    //                 BOX_WIDTH as i32,
    //                 BOX_HEIGHT as i32,
    //                 draw_color,
    //             );
    //         }
    //     }

    //     // selection is distinct from cursor, so draw it.
    //     if selection.cursor_x != selection.anchor_x || selection.cursor_y != selection.anchor_y {
    //         d.draw_rectangle(
    //             select_anchor_draw_x as i32,
    //             select_anchor_draw_y as i32,
    //             BOX_WIDTH as i32,
    //             BOX_HEIGHT as i32,
    //             BOX_SELECTED_BACKGROUND_COLOR,
    //         );
    //     }

    //     d.draw_rectangle(
    //         cursor_draw_x,
    //         cursor_draw_y,
    //         (BOX_WIDTH * 2) / 10 as i32,
    //         BOX_HEIGHT as i32,
    //         BOX_CURSORED_COLOR,
    //     );

    //     for x in 0u64..8 {
    //         for y in 0u64..100 {
    //             let draw_x = logical_x_to_draw_x(x as f32);
    //             let draw_y = logical_y_to_draw_y(y as f32);

    //             match track.get_note_from_coord(x, y) {
    //                 Some(note) => {
    //                     let text_color = if (note.x == x && note.y == y) {
    //                         TEXT_COLOR_LEADING
    //                     } else {
    //                         TEXT_COLOR_FOLLOWING
    //                     };
    //                     d.draw_text(
    //                         &format!("{}", note.to_str()),
    //                         draw_x as i32 + 5,
    //                         draw_y as i32 + 5,
    //                         20,
    //                         text_color,
    //                     );

    //                     let OCTAVE_TEXT_HEIGHT = 10;
    //                     let OCTAVE_TEXT_PADDING = 2;
    //                     let octave_text_len =
    //                         d.measure_text(&format!("{}", note.octave), OCTAVE_TEXT_HEIGHT);
    //                     d.draw_text(
    //                         &format!("{}", note.octave),
    //                         draw_x as i32 + BOX_WIDTH - octave_text_len - OCTAVE_TEXT_PADDING,
    //                         draw_y as i32 + BOX_HEIGHT - OCTAVE_TEXT_HEIGHT - OCTAVE_TEXT_PADDING,
    //                         OCTAVE_TEXT_HEIGHT,
    //                         Color::new(100, 255, 0, 255),
    //                     );
    //                 }
    //                 None => (),
    //             };
    //         }
    //     }

    //     d.draw_rectangle(
    //         0 as i32,
    //         (nowPlayingYEaser.get() - cameraYEaser.get()) as i32,
    //         BOX_NOW_PLAYING_SUGAR_WIDTH as i32,
    //         BOX_HEIGHT as i32,
    //         BOX_NOW_PLAYING_COLOR,
    //     );

    //     {
    //         let text = format!("Playback Speed: {:.1}", sequencerPlaybackSpeed.value);
    //         let width = d.measure_text(text.as_str(), 20);
    //         d.draw_text(
    //             &text,
    //             d.get_screen_width() as i32 - width as i32 - 20,
    //             PLAYBACK_SPEED_INFO_Y,
    //             20,
    //             PLAYBACK_SPEED_TEXT_COLOR,
    //         );
    //     }
    // }
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

// TODO: implement file drag and drop with rl::IsFileDropped: https://github.com/raysan5/raylib/blob/master/examples/core/core_drop_files.c

fn main() {
    // match testMidiInOpZ() {
    //     Ok(_) => (),
    //     Err(err) => println!("Error: {}", err),
    // };
    mainLoop();
}
