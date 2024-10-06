#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")] // hide console window on Windows in release
#![allow(rustdoc::missing_crate_level_docs)] // it's an example


use egui::Key;

use rand::seq::SliceRandom; // 0.7.2
use rfd::FileDialog;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

use std::error::Error;
use std::path::{PathBuf};

use std::sync::Mutex;
use std::thread::{current, sleep};
use std::{fs::File, sync::Arc};
use tinyaudio::prelude::*;
use tinyaudio::{run_output_device, OutputDeviceParameters};
use eframe::egui;
use egui::*;


const GOLDEN_RATIO: f32 = 1.618_034;

use midir::{Ignore, MidiInput, MidiInputPort};
use rustysynth::{SoundFont, Synthesizer, SynthesizerSettings};
use std::io::{stdin, stdout, Write};
use tracing::{event, Level};
use tracing_subscriber::layer::SubscriberExt;

mod datastructures;
mod midi;
mod counterpoint1;

use midi::*;
use datastructures::*;


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

fn settings_file_path() -> PathBuf {
    let mut filename = "monodrone-settings.json";
    let mut out = directories::UserDirs::new().unwrap().audio_dir().unwrap().to_path_buf();
    out.push(filename);
    std::fs::create_dir_all(&out).unwrap();
    out.push(filename);
    out
}
// TODO: read midi


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
        out
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
            value,
        }
    }

    fn update_seq(&mut self, seq: u64) -> bool {
        let updated = seq != self.seq;
        self.seq = seq;
        updated
    }

    fn set_value(&mut self, value: T) {
        self.value = value;
    }
}


fn save (egui_ctx : Option<&egui::Context>, monodrone_ctx : &datastructures::Context) {
    let str = ron::to_string(monodrone_ctx).unwrap();
    let file_path_str = monodrone_ctx.file_path.to_string_lossy();
    event!(Level::INFO, "saving file to path: '{}'", file_path_str.as_str());
    match File::create(monodrone_ctx.file_path.as_path()) {
        Ok(mut file) => {
            file.write_all(str.as_bytes()).unwrap();
            event!(Level::INFO, "Successfully saved '{}'", file_path_str.as_str());
            if let Some(egui_ctx) = egui_ctx {
                egui_ctx.send_viewport_cmd(ViewportCommand::Title(monodrone_ctx.get_app_title()));
            }
        }
        Err(e) => {
            event!(Level::ERROR, "Error saving file: {:?}", e);
            rfd::MessageDialog::new()
                .set_level(rfd::MessageLevel::Error)
                .set_title(format!(
                    "Unable to save file to path '{}'.",
                    file_path_str
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
    let (header, tracks) = monodrone_ctx.to_smf();
    match midly::write_std(&header, tracks.iter(), midi_file) {
        Ok(()) => {
            event!(Level::INFO, "Sucessfully saved MIDI file '{}'", midi_filepath.to_string_lossy());
        }
        Err(e) => {
            rfd::MessageDialog::new()
                .set_level(rfd::MessageLevel::Error)
                .set_title("Unable to save MIDI file")
                .set_description(e.to_string())
                .show();
            event!(Level::ERROR, "error writing MIDI file: {:?}", e);
        }
    };
}

fn load_monodrone_ctx_from_file (file_path : &PathBuf) -> Option<datastructures::Context> {
    match File::open(file_path.clone()) {
        Ok(file) => {
            let reader = std::io::BufReader::new(file);
            let str = std::io::read_to_string(reader).unwrap();
            event!(Level::INFO, "loaded file data.");
            let monodrone_ctx : datastructures::Context =  match ron::from_str(&str) {
                Ok(ctx) => {
                    ctx
                }

                Err(e) => {
                    rfd::MessageDialog::new()
                        .set_level(rfd::MessageLevel::Error)
                        .set_title("Unable to load file, JSON parsing error.")
                        .set_description(&e.to_string())
                        .show();
                    event!(Level::ERROR, "error loading file: {:?}", e);
                    return Option::None;
                }
            };
            event!(Level::INFO, "loaded file!");
            Option::Some(monodrone_ctx)
        }
        Err(e) => {
            event!(Level::ERROR, "error opening monodrone_ctx file '{:?}': {:?}", file_path, e);
            Option::None
        }
    }
}

fn open(egui_ctx: Option<&egui::Context>, monodrone_ctx : &datastructures::Context) -> Option<datastructures::Context> {
    let open_dialog = FileDialog::new()
        .add_filter("monodrone", &["drn"])
        .set_can_create_directories(true)
        .set_title("Open monodrone file location")
        .set_directory(monodrone_ctx.file_path.as_path().parent().unwrap());

    if let Some(path) = open_dialog.pick_file() {
        // open path and load string.
        event!(Level::INFO, "loading file {path:?}");
        match load_monodrone_ctx_from_file(&path) {
            Some(new_ctx) => {
                if let Some (egui_ctx) = egui_ctx {
                    egui_ctx.send_viewport_cmd(ViewportCommand::Title(new_ctx.get_app_title()));
                }
                Option::Some(new_ctx)
            }
            None => Option::None
        }
    }
    else {
        Option::None
    }
}

#[derive(Debug, Deserialize, Serialize)]
struct Settings {
    settings_file_path : PathBuf,
    current_file_path : PathBuf
}


impl Settings {
    pub fn new (settings_file_path : PathBuf, current_file_path : PathBuf) -> Self {
        Settings {
            settings_file_path : settings_file_path,
            current_file_path : current_file_path
        }
    }

    pub fn load(settings_file_path : PathBuf, new_file_path : PathBuf) -> Self {
        match File::open(settings_file_path.clone()) {
            Ok(file) => {
                event!(Level::INFO, "loaded settings file from : {:?}", settings_file_path);
                let reader = std::io::BufReader::new(file);
                let str = std::io::read_to_string(reader).unwrap();
                match ron::from_str(&str) {
                    Ok(settings) => {
                        event!(Level::INFO, "loaded settings file: {:?}", settings);
                        settings
                    }
                    Err(e) => {
                        event!(Level::ERROR, "error loading settings file: {:?}", e);
                        Settings::new(settings_file_path, new_file_path)
                    }
                }
            }
            Err(e) => {
                event!(Level::ERROR, "error opening settings file: {:?}", e);
                Settings::new(settings_file_path, new_file_path)
            }
        }
    }

    // save the settings to the settings file.
    pub fn save(&self) {
        let str = ron::to_string(self).unwrap();
        match File::create(self.settings_file_path.as_path()) {
            Ok(mut file) => {
                file.write_all(str.as_bytes()).unwrap();
                event!(Level::INFO, "Successfully saved settings file to path {:?}", self.settings_file_path);
            }
            Err(e) => {
                event!(Level::ERROR, "Error saving settings file: {:?}", e);
            }
        };
    }
}

fn mainLoop() {


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

    // TODO: call this AppState, have it manage the set of monodrone contexts?
    let mut settings = Settings::load(settings_file_path(), launch_file_path());

    let mut monodrone_ctx =
        if let Some (ctx) = load_monodrone_ctx_from_file(&settings.current_file_path) {
            ctx
        } else {
            let new_file_path = launch_file_path();
            settings.current_file_path = new_file_path;
            settings.save();
            datastructures::Context::new(launch_file_path())
        };
    save(None, &monodrone_ctx);

    event!(
        Level::INFO,
        "initial file path: {:?}",
        monodrone_ctx.file_path.to_string_lossy(),
    );


    let mut debounceMovement = Debouncer::new(80.0 / 1000.0);
    let mut debounceUndo = Debouncer::new(150.0 / 1000.0);

    let mut cameraEaser = Easer::new(Vec2::ZERO);
    let mut nowPlayingEaser = Easer::new(Pos2::ZERO);
    let mut cursorEaser = Easer::new(Pos2::ZERO);

    nowPlayingEaser.damping = 0.1;

    let mut file_name_buffer = monodrone_ctx.file_path.file_stem().unwrap().to_string_lossy().to_string();


    let _ = eframe::run_simple_native(format!("monodrone({})", monodrone_ctx.file_path.as_path().to_string_lossy()).as_str(),
        options, move |ctx, _frame| {

        egui::TopBottomPanel::bottom("Configuration").show(ctx, |ui| {
            ui.with_layout(Layout::left_to_right(Align::Center), |ui| {
                ui.label("Playback Speed");
                if ui.add(egui::DragValue::new(&mut monodrone_ctx.playback_speed).clamp_range(0.01..=3.0).update_while_editing(false).speed(0.05)).changed() {
                    sequencer_io.set_playback_speed(monodrone_ctx.playback_speed as f32);
                    event!(Level::INFO, "new Playback speed: {:?}", monodrone_ctx.playback_speed);
                }
                ui.label("Time Signature");
                ui.add(egui::DragValue::new(&mut monodrone_ctx.time_signature.0)
                    .clamp_range(1..=9).update_while_editing(false));
                ui.label("/");
                ui.add(egui::DragValue::new(&mut monodrone_ctx.time_signature.1)
                    .clamp_range(1..=9).update_while_editing(false));
                ui.label("Artist");
                ui.text_edit_singleline(&mut monodrone_ctx.artist_name);
                ui.label("Title");
                ui.text_edit_singleline(&mut monodrone_ctx.track_name);


            });
        });

        egui::TopBottomPanel::top("top bar").show(ctx, |ui| {
            egui::menu::bar(ui, |ui| {
                ui.label("File Name");
                if ui.text_edit_singleline(&mut file_name_buffer).changed() {
                    // reuse the same file path, but change the file name.
                    match monodrone_ctx.file_path.as_path().parent() {
                        Some(parent) => {
                            monodrone_ctx.file_path = parent.join(file_name_buffer.clone() + ".drn");
                            settings.current_file_path = monodrone_ctx.file_path.clone();
                            settings.save();
                        }
                        None => {}
                    };
                }
                ui.separator();
                if ui.button("New").clicked() {
                    monodrone_ctx = datastructures::Context::new(launch_file_path());
                    ctx.send_viewport_cmd(ViewportCommand::Title(monodrone_ctx.get_app_title()));
                }
                if ui.button("Open").clicked() {
                    if let Some(new_ctx) = open(Some(ctx), &monodrone_ctx) {
                        monodrone_ctx = new_ctx;
                    }
                }
                if ui.button("Save").clicked() {
                    // TODO: do this with a 'dirty' flag on AppSettings, dedup calls to settings.save()
                    save(Some(ctx), &monodrone_ctx);
                    settings.save();
                }
                // TODO: give a way to keep the file name as an editable value.
                // if ui.text_edit_singleline(monodrone_ctx.file_path).changed() {
                //     event!(Level::INFO, "file path changed");
                // }
            });
        });
        egui::CentralPanel::default().show(ctx, |ui| {
            // return;
            // let time_elapsed = rl.get_frame_time();
            let time_elapsed = 0.01; // TODO: fix this!
            debounceMovement.add_time_elapsed(time_elapsed);
            debounceUndo.add_time_elapsed(time_elapsed);


            // TODO: refactor into a widget that requests focus.
            if ui.ui_contains_pointer() && ui.is_enabled() && !ctx.wants_keyboard_input() { //response.hovered() {
                if ui.input(|i|  i.key_pressed(Key::C)) {
                    monodrone_ctx.set_pitch(datastructures::PitchName::C);
                }
                if ui.input(|i| i.key_pressed(Key::D)) {
                    monodrone_ctx.set_pitch(datastructures::PitchName::D);
                }
                if ui.input(|i| i.key_pressed(Key::E)) {
                    monodrone_ctx.set_pitch(datastructures::PitchName::E);
                }
                if ui.input(|i| i.key_pressed(Key::F)) {
                    monodrone_ctx.set_pitch(datastructures::PitchName::F);
                }
                if ui.input(|i| i.key_pressed(Key::G)) {
                    monodrone_ctx.set_pitch(datastructures::PitchName::G);
                }
                if ui.input(|i| i.key_pressed(Key::A)) {
                    monodrone_ctx.set_pitch(datastructures::PitchName::A);
                }
                if ui.input(|i| i.key_pressed(Key::B)) {
                    monodrone_ctx.set_pitch(datastructures::PitchName::B);
                }
                // <space>: plause/play
                if ui.input(|i| i.key_pressed(Key::Space)) {
                    if sequencer_io.is_playing() {
                        sequencer_io.stop();
                    } else {
                        let end_instant = monodrone_ctx.track.get_last_instant() as u64;
                        sequencer_io.set_track(monodrone_ctx.track.clone());
                        let start_instant = 0;
                        let is_looping = false;
                        sequencer_io.restart(start_instant, end_instant + 1, is_looping);
                    }
                }

                // P: play from current location? TODO: implement looping.
                if ui.input(|i| i.key_pressed(Key::P)) {
                    if sequencer_io.is_playing() {
                        sequencer_io.stop();
                    } else {
                        let end_instant = monodrone_ctx.track.get_last_instant() as u64;
                        sequencer_io.set_track(monodrone_ctx.track.clone());
                        let start_instant = 0;
                        let is_looping = false;
                        sequencer_io.restart(start_instant, end_instant + 1, is_looping);
                    }
                }

                if ui.input(|i| i.key_pressed(Key::H)) {
                    if ui.input(|i| i.modifiers.shift || i.modifiers.command || i.modifiers.ctrl) {
                        monodrone_ctx.lower_octave();
                    }
                    else {
                        monodrone_ctx.cursor_move_left_one();
                    }
                }
                if ui.input(|i| i.key_pressed(Key::J)) {
                    if ui.input(|i| i.modifiers.shift || i.modifiers.command || i.modifiers.ctrl) {
                        monodrone_ctx.increase_nsteps();
                    }
                    else {
                        monodrone_ctx.cursor_move_down_one();
                    }
                }
                if ui.input(|i| i.key_pressed(Key::K)) {
                    if ui.input(|i| i.modifiers.shift || i.modifiers.command || i.modifiers.ctrl) {
                        monodrone_ctx.decrease_nsteps();
                    }
                    else {
                        monodrone_ctx.cursor_move_up_one();
                    }
                }
                if ui.input(|i| i.key_pressed(Key::L)) {
                    if ui.input(|i| i.modifiers.shift || i.modifiers.command || i.modifiers.ctrl) {
                        monodrone_ctx.raise_octave();
                    } else {
                        monodrone_ctx.cursor_move_right_one();
                    }
                }
                if ui.input(|i| i.key_pressed(Key::Backspace)) {
                    monodrone_ctx.delete_line();
                }
                if ui.input(|i| i.key_pressed(Key::S) && i.modifiers.command) {
                    save(Some(ctx), &monodrone_ctx);
                    settings.current_file_path = monodrone_ctx.file_path.clone();
                    settings.save();
                }
                if ui.input(|i| i.key_pressed(Key::O) && i.modifiers.command) {
                    if let Some(new_ctx) = open(Some(ctx), &monodrone_ctx) {
                        monodrone_ctx = new_ctx;
                        settings.current_file_path = monodrone_ctx.file_path.clone();
                        settings.save();
                    }
                }

                if ui.input(|i| i.key_pressed(Key::Z) && i.modifiers.command) {
                    if ui.input(|i| i.modifiers.shift) {
                        monodrone_ctx.redo_action();
                    } else {
                        monodrone_ctx.undo_action();
                    }
                }
                if ui.input (|i| i.key_pressed(Key::Num2)) {
                    monodrone_ctx.toggle_flat();
                }
                if ui.input (|i| i.key_pressed(Key::Num3)) {
                    monodrone_ctx.toggle_sharp();
                }
                if ui.input (|i| i.key_pressed(Key::Enter)) {
                    monodrone_ctx.newline();
                }
            }

            // let (response, painter) = ui.allocate_painter(size, Sense::hover());
            let painter = ui.painter_at(ui.available_rect_before_wrap());

            let box_dim = Vec2::new(25., 25.);
            let box_padding_min = Vec2::new(3., 3.);
            let box_padding_max = Vec2::new(3., 3.);
            let window_padding = Vec2::new(10.0, box_padding_min.y);
            let sidebar_left_width = 15.0;
            let avail_rect = ui.available_rect_before_wrap();

            let box_deselected_color = egui::Color32::from_rgb(66, 66, 66);
            let _box_selected_background_color = egui::Color32::from_rgb(255, 0, 100);
            let box_cursored_color = egui::Color32::from_rgb(189, 189, 189);
            let box_cursor_color = egui::Color32::from_rgb(250, 250, 250);
            let box_now_playing_color = egui::Color32::from_rgb(255, 143, 0);
            let text_color_leading = egui::Color32::from_rgb(207, 216, 220);
            let text_color_following = egui::Color32::from_rgb(99, 99, 99);

            let font_size_note : f32 = 10.0;
            let font_size_octave : f32 = 10.0;

            cameraEaser.set(Vec2::new(0.,
                (monodrone_ctx.selection.cursor().y *
                    (box_dim.y + box_padding_min.y + box_padding_max.y) - avail_rect.height() * 0.5).max(0.0))
            );
            cameraEaser.step();



            let logical_to_sidebar_text_min = |logical: egui::Pos2| -> egui::Pos2 {
                avail_rect.min + window_padding +
                logical.to_vec2() * (box_dim + box_padding_min + box_padding_max) - cameraEaser.get()
            };

            // now playing.
            let logical_to_draw_min = |logical: egui::Pos2| -> egui::Pos2 {
                avail_rect.min + window_padding + Vec2::new(sidebar_left_width, 0.0) +
                logical.to_vec2() * (box_dim + box_padding_min + box_padding_max) - cameraEaser.get()
            };


            {
                let cur_instant = sequencer_io.sequencer.lock().as_ref().unwrap().cur_instant;
                let now_playing_box_y : i32 = cur_instant as i32 - 1;
                nowPlayingEaser.set(logical_to_draw_min(Pos2::new(0., now_playing_box_y as f32)));
                nowPlayingEaser.step();
            }

            for x in 0u64..datastructures::NTRACKS {
                for y in 0u64..datastructures::TRACK_LENGTH {
                    let draw = logical_to_draw_min(Pos2::new(x as f32, y as f32));
                    painter.rect_filled (Rect::from_min_size(draw, box_dim),
                        egui::Rounding::default().at_least(2.0),
                        box_deselected_color);
                }
            }

            // TODO: for the love of got, clean this up.
            let cursor_dim = box_dim * Vec2::new(1., 0.2);
            let cursor_box_top_left = logical_to_draw_min(monodrone_ctx.selection.cursor());

            // place cursor at *end* of the box, if the box is filled.
            let cursor_loc =
                if monodrone_ctx.track.get_note_from_coord(monodrone_ctx.selection.x, monodrone_ctx.selection.y).is_some() {
                    cursor_box_top_left + box_dim - cursor_dim
                } else {
                    cursor_box_top_left
                };
            cursorEaser.set(cursor_loc);
            cursorEaser.damping = 0.08; cursorEaser.step();
            let cursor_loc = cursorEaser.get();


            let draw = logical_to_draw_min(Pos2::new(monodrone_ctx.selection.x as f32, monodrone_ctx.selection.y as f32));
            painter.rect_filled (Rect::from_min_size(draw, box_dim),
                egui::Rounding::default().at_least(2.0),
                box_cursored_color);

            painter.rect_filled (Rect::from_min_size(cursor_loc, cursor_dim),
                Rounding::default().at_least(2.0),
                box_cursor_color);

            for y in 0u64..100 {
                let draw = logical_to_sidebar_text_min(Pos2::new(0f32, y as f32));
                painter.text(draw, Align2::LEFT_TOP, &format!("{:02}", y), FontId::monospace(font_size_note), text_color_following);
            }

            for x in 0u64..8 {
                for y in 0u64..100 {
                    let draw = logical_to_draw_min(Pos2::new(x as f32, y as f32));
                    if let Some(note) = monodrone_ctx.track.get_note_from_coord(x, y) {
                        let text_color = if note.x == x && note.y() == y {
                            text_color_leading
                        } else {
                            text_color_following
                        };

                        let note_text_padding = Vec2::splat(5.0);
                        painter.text(draw + note_text_padding,
                            Align2::LEFT_TOP, note.to_str(), FontId::monospace(font_size_note), text_color);
                        let octave_text_padding = Vec2::new(2., 2.);
                        let octave_text_color = egui::Color32::from_rgb(104, 159, 56);
                        let octave_text = painter.layout_no_wrap(note.octave.to_string(),
                            FontId::monospace(font_size_octave), octave_text_color);
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

// represents a connection to an Op-z instance
struct Opz {
    // port : Option<MidiInputPort>, // MIDI input port.
    conn : Option<midir::MidiInputConnection<()>>,
}

impl Opz {
    fn new() -> Opz {
        event!(Level::INFO, "making new OP-Z.");

        Opz {
            // port: None,
            conn : None,

        }
    }

    fn find_port(&mut self) {
        event!(Level::INFO, "finding OP-Z...");

        let mut midi_in = MidiInput::new("midir reading input").unwrap();
        midi_in.ignore(Ignore::None);

        let in_ports = midi_in.ports();

        let mut port = None;
        for p in in_ports {
            if midi_in.port_name(&p).unwrap() == "OP-Z" {
                port = Some(p);
            }
        };

        self.conn = if let Some(p) = port {
            event!(Level::INFO, "found OP-Z!");
            midi_in.connect(
                &p,
                "midir-read-input",
                move |stamp, message, _| {
                    event!(Level::INFO, "message received from OP-Z. message: {:?}", message);
                    if message.len() <= 1 {
                        return;
                    }
                    println!("{}: {:?} (len = {})", stamp, message, message.len());
                },
                (),
            ).ok()
        } else {
            event!(Level::INFO, "Unable to find OP-Z.");
            None
        };

        // while true {
        //     sleep(core::time::Duration::from_secs(1));
        // };
    }
}

fn testMidiInOpZ() -> Result<MidiInputPort, Box<dyn Error>> {
    let mut input = String::new();

    let mut midi_in = MidiInput::new("midir reading input")?;
    midi_in.ignore(Ignore::None);

    // Get an input port (read from console if multiple are available)
    let in_ports = midi_in.ports();
    let opz_opt = {
        let mut out = None;
        for port in in_ports {
            if midi_in.port_name(&port).unwrap() == "OP-Z" {
                out = Some(port);
            }
        }
        out
    };

    let opz = match opz_opt  {
        None => {
        event!(Level::INFO, "Unable to find OP-Z.");
        return Err("OP-Z not found".into());
        },
        Some(port) => {
            event!(Level::INFO, "found OP-Z!");
            port
        }
    };

    let conn = midi_in.connect(
        &opz,
        "midir-read-input",
        move |stamp, message, _| {
            event!(Level::INFO, "message received from OP-Z. message: {:?}", message);
            if message.len() <= 1 {
                return;
            }
            println!("{}: {:?} (len = {})", stamp, message, message.len());
        },
        (),
    ).unwrap();


    input.clear();
    stdin().read_line(&mut input)?; // wait for next enter key press

    while true {
        sleep(core::time::Duration::from_secs(1));
    };

    // 463667691423: [181, 1/2/3/4, value]: 4 scroll wheels (len = 3)
    // keys: [149, 65...(key number), 0/100 up/down]: 65-69
    //
    println!("Closing connection");
    panic!("done");
    Ok(opz)
}

// TODO: implement file drag and drop with rl::IsFileDropped: https://github.com/raysan5/raylib/blob/master/examples/core/core_drop_files.c

fn main() {
    tracing_subscriber::fmt().init();
    let _ = tracing::subscriber::set_global_default(
        tracing_subscriber::registry().with(tracing_tracy::TracyLayer::default()),
    );
    // testMidiInOpZ();

    // let mut opz = Opz::new();
    // opz.find_port();
    mainLoop();
}
