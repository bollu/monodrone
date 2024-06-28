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
use monodroneffi::{PlayerNote, Selection, TrackBuilder, UITrack};
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


fn launch_file_path() -> PathBuf {
    let mut filename = whimsical_file_name();
    filename.push_str(".drn");
    let mut out = directories::UserDirs::new().unwrap().audio_dir().unwrap().to_path_buf();
    out.push("Monodrone");
    std::fs::create_dir_all(&out).unwrap();
    out.push(filename);
    out
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

struct Easer<T> where {
    pub target: T,
    cur: T,
    pub damping: f32,
}

impl<T, D> Easer<T>
where
    D : Copy + std::ops::Mul<f32, Output = D>, // delta
    T: Copy + std::ops::Add<D, Output = T> + std::ops::Sub<Output = D>, {

    fn new(value: T) -> Easer<T> {
        Easer {
            target: value,
            cur: value,
            damping: 0.2,
        }
    }

    fn get(&self) -> T {
        self.cur
    }

    fn set(&mut self, value: T) {
        self.target = value;
    }

    fn step(&mut self) {
        self.cur = self.cur + ((self.target - self.cur) * self.damping);
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

    fn set_playback_speed(&mut self, instant_delta: f32) {
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

fn save (egui_ctx : &egui::Context, monodrone_ctx : &monodroneffi::Context) {
    let str = monodrone_ctx.to_json_string();
    let file_path_str = monodrone_ctx.file_path().to_string_lossy();
    event!(Level::INFO, "saving file to path: '{}'", file_path_str.as_str());
    match File::create(monodrone_ctx.file_path().as_path()) {
        Ok(mut file) => {
            file.write_all(str.as_bytes()).unwrap();
            event!(Level::INFO, "Successfully saved '{}'", file_path_str.as_str());
            egui_ctx.send_viewport_cmd(ViewportCommand::Title(monodrone_ctx.get_app_title()));
        }
        Err(e) => {
            event!(Level::ERROR, "Error saving file: {:?}", e);
            rfd::MessageDialog::new()
                .set_level(rfd::MessageLevel::Error)
                .set_title(format!(
                    "Unable to save file to path '{}'.",
                    file_path_str.to_string()
                ))
                .set_description(e.to_string())
                .show();
        }
    };
    let midi_filepath = monodrone_ctx.get_midi_export_file_path();
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
    let player_track = monodrone_ctx.track().to_player_track();
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

fn open(ctx: &egui::Context, monodrone_ctx : &monodroneffi::Context) -> Option<monodroneffi::Context> {
    let open_dialog = FileDialog::new()
        .add_filter("monodrone", &["drn"])
        .set_can_create_directories(true)
        .set_title("Open monodrone file location")
        .set_directory(monodrone_ctx.file_path().as_path().parent().unwrap());

    if let Some(path) = open_dialog.pick_file() {
        // open path and load string.
        event!(Level::INFO, "loading file {path:?}");
        match File::open(path.clone()) {
            Ok(file) => {
                let reader = std::io::BufReader::new(file);
                let str = std::io::read_to_string(reader).unwrap();
                event!(Level::INFO, "loaded file data: {str}");
                let monodrone_ctx = match monodroneffi::ctx_from_json_str(str) {
                    Ok(raw_ctx) => {
                        monodroneffi::Context::from_raw_ctx(raw_ctx, path)
                    }

                    Err(e) => {
                        rfd::MessageDialog::new()
                            .set_level(rfd::MessageLevel::Error)
                            .set_title("Unable to load file, JSON parsing error.")
                            .set_description(&e)
                            .show();
                        event!(Level::ERROR, "error loading file: {:?}", e);
                        return Option::None;
                    }
                };
                event!(Level::INFO, "loaded file!");
                // TODO: figure out how to sync this properly.
                // There is an annoying cyclic dependency: we can only send a viewport command
                // after we have a context, but we must create a global monodrone_ctx before we
                // get our hands on a real context object.
                ctx.send_viewport_cmd(ViewportCommand::Title(monodrone_ctx.get_app_title()));
                Option::Some(monodrone_ctx)
            }
            Err(e) => {
                event!(Level::ERROR, "error opening file: {:?}", e);
                Option::None
            }
        }
    }
    else {
        Option::None
    }
}

fn mainLoop() {
    tracing_subscriber::fmt().init();
    let _ = tracing::subscriber::set_global_default(
        tracing_subscriber::registry().with(tracing_tracy::TracyLayer::default()),
    );

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
    let options = eframe::NativeOptions {
        viewport: egui::ViewportBuilder::default()
            .with_maximized(true)
            .with_icon(eframe::icon_data::from_png_bytes(include_bytes!("../favicon.png")).unwrap()),
        ..Default::default()
    };

    event!(Level::INFO, "creating context");

    let mut monodrone_ctx = monodroneffi::Context::new(launch_file_path());
    event!(
        Level::INFO,
        "initial file path: {:?}",
        monodrone_ctx.file_path().to_string_lossy(),
    );

    let mut debounceMovement = Debouncer::new(80.0 / 1000.0);
    let mut debounceUndo = Debouncer::new(150.0 / 1000.0);

    let mut cameraEaser = Easer::new(Vec2::ZERO);
    let mut nowPlayingEaser = Easer::new(Pos2::ZERO);
    let mut cursorEaser = Easer::new(Pos2::ZERO);

    let mut playback_speed = 1.0 as f64;
    nowPlayingEaser.damping = 0.1;

    let mut time_signature = (4, 4);
    let mut artist : String = "monodrone".to_string();
    let mut song_name : String = "aria".to_string();
    let _ = eframe::run_simple_native(format!("monodrone({})", monodrone_ctx.file_path().to_str().unwrap()).as_str(),
        options, move |ctx, _frame| {
        egui::TopBottomPanel::bottom("Configuration").show(ctx, |ui| {
            ui.with_layout(Layout::left_to_right(Align::Center), |ui| {
                ui.label("Playback Speed");
                if ui.add(egui::DragValue::new(&mut playback_speed).clamp_range(0.01..=3.0).update_while_editing(false).speed(0.05)).changed() {
                    monodrone_ctx.set_playback_speed(playback_speed);
                    sequencer_io.set_playback_speed(playback_speed as f32);
                    event!(Level::INFO, "new Playback speed: {:?}", playback_speed);
                }
                ui.label("Time Signature");
                if ui.add(egui::DragValue::new(&mut time_signature.0).clamp_range(1..=9).update_while_editing(false)).changed() {
                }
                ui.label("/");
                if ui.add(egui::DragValue::new(&mut time_signature.1).clamp_range(1..=9).update_while_editing(false)).changed() {
                }
                ui.label("Artist");
                ui.text_edit_singleline(&mut artist);
                ui.label("Title");
                ui.text_edit_singleline(&mut song_name);
            });
        });

        egui::TopBottomPanel::top("top bar").show(ctx, |ui| {
            egui::menu::bar(ui, |ui| {
                if ui.button("New").clicked() {
                    monodrone_ctx = monodroneffi::Context::new(launch_file_path());
                    ctx.send_viewport_cmd(ViewportCommand::Title(monodrone_ctx.get_app_title()));
                }
                if ui.button("Open").clicked() {
                    if let Some(new_ctx) = open(&ctx, &monodrone_ctx) {
                        monodrone_ctx = new_ctx;
                    }
                }
                if ui.button("Save").clicked() {
                    save(&ctx, &monodrone_ctx);
                }
            });
        });
        egui::CentralPanel::default().show(ctx, |ui| {
            // return;
            // let time_elapsed = rl.get_frame_time();
            let time_elapsed = 0.01; // TODO: fix this!
            debounceMovement.add_time_elapsed(time_elapsed);
            debounceUndo.add_time_elapsed(time_elapsed);

            // TODO: refactor into a widget that requests focus.
            if ctx.input(|i| i.key_pressed(Key::C)) {
                monodrone_ctx.set_pitch(monodroneffi::PitchName::C);
            }
            if ctx.input(|i| i.key_pressed(Key::D)) {
                monodrone_ctx.set_pitch(monodroneffi::PitchName::D);
            }
            if ctx.input(|i| i.key_pressed(Key::E)) {
                monodrone_ctx.set_pitch(monodroneffi::PitchName::E);
            }
            if ctx.input(|i| i.key_pressed(Key::F)) {
                monodrone_ctx.set_pitch(monodroneffi::PitchName::F);
            }
            if ctx.input(|i| i.key_pressed(Key::G)) {
                monodrone_ctx.set_pitch(monodroneffi::PitchName::G);
            }
            if ctx.input(|i| i.key_pressed(Key::A)) {
                monodrone_ctx.set_pitch(monodroneffi::PitchName::A);
            }
            if ctx.input(|i| i.key_pressed(Key::B)) {
                monodrone_ctx.set_pitch(monodroneffi::PitchName::B);
            }
            if ctx.input(|i| i.key_pressed(Key::Space)) {
                if sequencer_io.is_playing() {
                    sequencer_io.stop();
                } else {
                    sequencer_io.set_track(monodrone_ctx.track().clone().to_player_track());
                    let end_instant = monodrone_ctx.track().get_last_instant() as u64;
                    let start_instant = 0;
                    let is_looping = false;
                    sequencer_io.restart(start_instant, end_instant + 1, is_looping);
                }
            }


            if ctx.input(|i| i.key_pressed(Key::H)) {
                if ctx.input(|i| i.modifiers.shift || i.modifiers.command || i.modifiers.ctrl) {
                    monodrone_ctx.lower_octave();
                }
                else {
                    monodrone_ctx.cursor_move_left_one();
                }
            }
            if ctx.input(|i| i.key_pressed(Key::J)) {
                if ctx.input(|i| i.modifiers.shift || i.modifiers.command || i.modifiers.ctrl) {
                    monodrone_ctx.increase_nsteps();
                }
                else {
                    monodrone_ctx.cursor_move_down_one();
                }
            }
            if ctx.input(|i| i.key_pressed(Key::K)) {
                if ctx.input(|i| i.modifiers.shift || i.modifiers.command || i.modifiers.ctrl) {
                    monodrone_ctx.decrease_nsteps();
                }
                else {
                    monodrone_ctx.cursor_move_up_one();
                }
            }
            if ctx.input(|i| i.key_pressed(Key::L)) {
                if ctx.input(|i| i.modifiers.shift || i.modifiers.command || i.modifiers.ctrl) {
                    monodrone_ctx.raise_octave();
                } else {
                    monodrone_ctx.cursor_move_right_one();
                }
            }
            if ctx.input(|i| i.key_pressed(Key::Backspace)) {
                if ctx.input(|i| i.modifiers.shift) {
                    monodrone_ctx.delete_line();
                } else {
                    monodrone_ctx.delete_note();
                }
            }
            if ctx.input(|i| i.key_pressed(Key::S) && i.modifiers.command) {
                save(&ctx, &monodrone_ctx);
            }
            if ctx.input(|i| i.key_pressed(Key::O) && i.modifiers.command) {
                if let Some(new_ctx) = open(&ctx, &monodrone_ctx) {
                    monodrone_ctx = new_ctx;
                }
            }

            if ctx.input(|i| i.key_pressed(Key::Z) && i.modifiers.command) {
                if ctx.input(|i| i.modifiers.shift) {
                    monodrone_ctx.redo_action();
                } else {
                    monodrone_ctx.undo_action();
                }
            }
            if ctx.input (|i| i.key_pressed(Key::Num2)) {
                monodrone_ctx.toggle_flat();
            }
            if ctx.input (|i| i.key_pressed(Key::Num3)) {
                monodrone_ctx.toggle_sharp();
            }
            if ctx.input (|i| i.key_pressed(Key::Enter)) {
                monodrone_ctx.newline();
            }

            // let (response, painter) = ui.allocate_painter(size, Sense::hover());
            let painter = ui.painter_at(ui.available_rect_before_wrap());

            let box_dim = Vec2::new(40., 40.);
            let box_padding_min = Vec2::new(5., 5.);
            let box_padding_max = Vec2::new(5., 5.);
            let window_padding = Vec2::new(box_padding_min.x, box_padding_min.y);
            let avail_rect = ui.available_rect_before_wrap();

            let box_deselected_color = egui::Color32::from_rgb(66, 66, 66);
            let box_selected_background_color = egui::Color32::from_rgb(255, 0, 100);
            let box_cursored_color = egui::Color32::from_rgb(99, 99, 99);
            let box_now_playing_color = egui::Color32::from_rgb(255, 143, 0);
            let text_color_leading = egui::Color32::from_rgb(207, 216, 220);
            let text_color_following = egui::Color32::from_rgb(99, 99, 99);

            cameraEaser.set(Vec2::new(0.,
                (monodrone_ctx.selection().cursor.y * (box_dim.y + box_padding_min.y + box_padding_max.y) - avail_rect.height() * 0.5).max(0.0))
            );
            cameraEaser.step();

            cursorEaser.set(monodrone_ctx.selection().cursor); cursorEaser.damping = 0.3; cursorEaser.step();

            // now playing.
            let logical_to_draw_min = |logical: egui::Pos2| -> egui::Pos2 {
                return avail_rect.min + window_padding +
                logical.to_vec2() * (box_dim + box_padding_min + box_padding_max) - cameraEaser.get();
            };


            {
                let cur_instant = sequencer_io.sequencer.lock().as_ref().unwrap().cur_instant;
                let now_playing_box_y : i32 = cur_instant as i32 - 1;
                nowPlayingEaser.set(logical_to_draw_min(Pos2::new(0., now_playing_box_y as f32)));
                nowPlayingEaser.step();
            }

            for x in 0u64..8 {
                for y in 0u64..100 {
                    let draw = logical_to_draw_min(Pos2::new(x as f32, y as f32));
                    painter.rect_filled (Rect::from_min_size(draw, box_dim),
                        egui::Rounding::default().at_least(4.0),
                        box_deselected_color);
                }
            }

            let cursor_draw = logical_to_draw_min(cursorEaser.get());
            painter.rect_filled (Rect::from_min_size(cursor_draw, box_dim * Vec2::new(0.2, 1.)),
                Rounding::default().at_least(2.0),
                box_cursored_color);

            for x in 0u64..8 {
                for y in 0u64..100 {
                    let draw = logical_to_draw_min(Pos2::new(x as f32, y as f32));
                    if let Some(note) = monodrone_ctx.track().get_note_from_coord(x, y) {
                            let text_color = if note.x == x && note.y == y {
                                text_color_leading
                            } else {
                                text_color_following
                            };

                            let note_text_padding = Vec2::splat(5.0);
                            painter.text(draw + note_text_padding,
                                Align2::LEFT_TOP, note.to_str(), FontId::monospace(20.), text_color);
                            let octave_text_padding = Vec2::new(2., 2.);
                            let octave_text_color = egui::Color32::from_rgb(104, 159, 56);
                            let octave_text = painter.layout_no_wrap(note.octave.to_string(),
                                FontId::monospace(15.), octave_text_color);
                            let text_pos = draw + box_dim - octave_text_padding - octave_text.rect.size();
                            painter.galley(text_pos, octave_text, octave_text_color);
                    };
                }
            }

            painter.rect_filled (Rect::from_min_size(nowPlayingEaser.get(),
                box_dim * Vec2::new(0.1, 1.0)),
                Rounding::default().at_least(4.0),
                box_now_playing_color);
            ctx.request_repaint();
        });

    });
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
