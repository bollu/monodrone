#![allow(rustdoc::missing_crate_level_docs)] // it's an example


use egui::Key;

use ron::de::from_reader;
use serde::{Deserialize, Serialize};
use rand::seq::SliceRandom; // 0.7.2
use ron;
use rfd::FileDialog;
use tracing_subscriber::fmt::MakeWriter;
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

fn audio_dir() -> PathBuf {
    let mut out = directories::UserDirs::new().unwrap().audio_dir().unwrap().to_path_buf();
    out.push("Monodrone");
    std::fs::create_dir_all(&out).unwrap();
    return out
}

fn ide_image_file_path() -> PathBuf {
    let mut out = audio_dir();
    let filename = "monodrone-settings.json";
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


// fn save (egui_ctx : Option<&egui::Context>, settings.ctx() : &datastructures::Context) {
//     let str = ron::to_string(settings.ctx()).unwrap();
//     let file_path_str = settings.ctx().file_path.to_string_lossy();
//     event!(Level::INFO, "saving file to path: '{}'", file_path_str.as_str());
//     match File::create(settings.ctx().file_path.as_path()) {
//         Ok(mut file) => {
//             file.write_all(str.as_bytes()).unwrap();
//             event!(Level::INFO, "Successfully saved '{}'", file_path_str.as_str());
//             if let Some(egui_ctx) = egui_ctx {
//                 egui_ctx.send_viewport_cmd(ViewportCommand::Title(settings.ctx().get_app_title()));
//             }
//         }
//         Err(e) => {
//             event!(Level::ERROR, "Error saving file: {:?}", e);
//             rfd::MessageDialog::new()
//                 .set_level(rfd::MessageLevel::Error)
//                 .set_title(format!(
//                     "Unable to save file to path '{}'.",
//                     file_path_str
//                 ))
//                 .set_description(e.to_string())
//                 .show();
//         }
//     };
//
//     let midi_filepath = settings.ctx().get_midi_export_file_path();
//     let midi_file = match File::create(midi_filepath.clone()) {
//         Ok(file) => file,
//         Err(e) => {
//             rfd::MessageDialog::new()
//                 .set_level(rfd::MessageLevel::Error)
//                 .set_title("Unable to create MIDI file")
//                 .set_description(e.to_string())
//                 .show();
//             event!(Level::ERROR, "error creating MIDI file: {:?}", e);
//             return;
//         }
//     };
//     let (header, tracks) = settings.ctx().to_smf();
//     match midly::write_std(&header, tracks.iter(), midi_file) {
//         Ok(()) => {
//             event!(Level::INFO, "Sucessfully saved MIDI file '{}'", midi_filepath.to_string_lossy());
//         }
//         Err(e) => {
//             rfd::MessageDialog::new()
//                 .set_level(rfd::MessageLevel::Error)
//                 .set_title("Unable to save MIDI file")
//                 .set_description(e.to_string())
//                 .show();
//             event!(Level::ERROR, "error writing MIDI file: {:?}", e);
//         }
//     };
// }

/*
fn load_settings(file_path : &PathBuf) -> Option<datastructures::Context> {
    match File::open(file_path.clone()) {
        Ok(file) => {
            let reader = std::io::BufReader::new(file);
            let str = std::io::read_to_string(reader).unwrap();
            event!(Level::INFO, "loaded file data.");
            let settings.ctx() : datastructures::Context =  match ron::from_str(&str) {
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
            Option::Some(settings.ctx())
        }
        Err(e) => {
            event!(Level::ERROR, "error opening settings.ctx() file '{:?}': {:?}", file_path, e);
            Option::None
        }
    }
}
*/

// fn open(egui_ctx: Option<&egui::Context>, settings.ctx() : &datastructures::Context) -> Option<datastructures::Context> {
//     let open_dialog = FileDialog::new()
//         .add_filter("monodrone", &["drn"])
//         .set_can_create_directories(true)
//         .set_title("Open monodrone file location")
//         .set_directory(settings.ctx().file_path.as_path().parent().unwrap());
//
//     if let Some(path) = open_dialog.pick_file() {
//         // open path and load string.
//         event!(Level::INFO, "loading file {path:?}");
//         match load_settings.ctx()_from_file(&path) {
//             Some(new_ctx) => {
//                 if let Some (egui_ctx) = egui_ctx {
//                     egui_ctx.send_viewport_cmd(ViewportCommand::Title(new_ctx.get_app_title()));
//                 }
//                 Option::Some(new_ctx)
//             }
//             None => Option::None
//         }
//     }
//     else {
//         Option::None
//     }
// }



// The image file, that has all the state.
#[derive(Debug, Serialize, Deserialize)]
struct IDEImage {
    contexts : Vec<datastructures::Context>,
    ix : i32,
}


pub fn save_context(ctx : &datastructures::Context) {
    // let midi_filepath = dir ctx.get_midi_export_file_path();
    let mut path = audio_dir();
    path.push(format!("{}.mid", ctx.track_name.clone()));

    let midi_file = match File::create(path.clone()) {
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
    let (header, tracks) = ctx.to_smf();
    match midly::write_std(&header, tracks.iter(), midi_file) {
        Ok(()) => {
            event!(Level::INFO, "Successfully saved MIDI file '{}'", path.to_string_lossy());
        }
        Err(e) => {
            rfd::MessageDialog::new()
                .set_level(rfd::MessageLevel::Error)
                .set_title("Unable to save MIDI file")
                .set_description(e.to_string())
                .show();
            event!(Level::ERROR, "error writing MIDI file: {:?}", e);
        }
    }
}


impl IDEImage {
    pub fn ctx_mut(&mut self) -> &mut datastructures::Context {
        &mut self.contexts[self.ix as usize]
    }

    // TODO: rename ctx to ctx_mut.
    pub fn ctx(&self) -> &datastructures::Context {
        &self.contexts[self.ix as usize]
    }

    pub fn load() -> Self {
        let default =
            IDEImage {
                contexts : vec![datastructures::Context::new("track-0".to_string())],
                ix : 0,
            };
        let path = ide_image_file_path();
        let file =
            match File::open(path.clone()) {
                Ok(file) => {
                    event!(Level::INFO, "opened settings fil at '{}'", path.to_string_lossy());
                    file
                }
                Err(err) => {
                    event!(Level::ERROR, "error loading settings file at '{}': {:?}", path.to_string_lossy(), err);
                    default.save();
                    return default
                }
            };

        let reader = std::io::BufReader::new(file);
        match ron::de::from_reader(reader) {
            Ok(settings) => {
                event!(Level::INFO, "loaded settings from file: {:?}", settings);
                return settings;
            }
            Err(err) => {
                event!(Level::ERROR, "failed to load settings file: '{:?}'", err);
                default.save();
                return default;
            }
        }
        default
    }

    pub fn new(&mut self, name : String) {
        let ix = self.contexts.len();
        let ctx = datastructures::Context::new(format!("track-{}", ix));
        self.contexts.push(ctx);
        self.ix = ix as i32;
    }

    // save the settings to the settings file.
    pub fn save(&self) {
        let path = ide_image_file_path();
        match File::create(path.clone()) {
            Ok(mut file) => {
                let mut writer = file.make_writer();
                ron::ser::to_writer(writer, &self).unwrap();
                event!(Level::INFO, "Successfully saved settings file to path {:?}", path.to_string_lossy());
            }
            Err(e) => {
                event!(Level::ERROR, "Error saving settings file '{}': {:?}", path.to_string_lossy(),
                    e);
            }
        }
        save_context(&self.ctx());
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
    let mut settings = IDEImage::load();


    let mut debounceMovement = Debouncer::new(80.0 / 1000.0);
    let mut debounceUndo = Debouncer::new(150.0 / 1000.0);

    let mut cameraEaser = Easer::new(Vec2::ZERO);
    let mut nowPlayingEaser = Easer::new(Pos2::ZERO);
    let mut cursorEaser = Easer::new(Pos2::ZERO);

    nowPlayingEaser.damping = 0.1;


    let _ = eframe::run_simple_native(format!("monodrone({})", settings.ctx_mut().track_name).as_str(),
        options, move |ctx, _frame| {

        egui::TopBottomPanel::bottom("Configuration").show(ctx, |ui| {
            ui.with_layout(Layout::left_to_right(Align::Center), |ui| {
                ui.label("Playback Speed");
                if ui.add(egui::DragValue::new(&mut settings.ctx_mut().playback_speed).clamp_range(0.01..=3.0).update_while_editing(false).speed(0.05)).changed() {
                    sequencer_io.set_playback_speed(settings.ctx_mut().playback_speed as f32);
                    event!(Level::INFO, "new Playback speed: {:?}", settings.ctx_mut().playback_speed);
                }
                ui.label("Time Signature");
                ui.add(egui::DragValue::new(&mut settings.ctx_mut().time_signature.0)
                    .clamp_range(1..=9).update_while_editing(false));
                ui.label("/");
                ui.add(egui::DragValue::new(&mut settings.ctx_mut().time_signature.1)
                    .clamp_range(1..=9).update_while_editing(false));
                ui.label("Artist");
                ui.text_edit_singleline(&mut settings.ctx_mut().artist_name);
                ui.label("Title");
                ui.text_edit_singleline(&mut settings.ctx_mut().track_name);


            });
        });

        egui::TopBottomPanel::top("top bar").show(ctx, |ui| {
            egui::menu::bar(ui, |ui| {
                if ui.button("New").clicked() {
                    // settings.ctx() = datastructures::Context::new(new_launch_file_path());
                    // ctx.send_viewport_cmd(ViewportCommand::Title(settings.ctx().get_app_title()));
                }
                // if ui.button("Open").clicked() {
                //     // if let Some(new_ctx) = open(Some(ctx), &settings.ctx()) {
                //     //     settings.ctx() = new_ctx;
                //     // }
                // }
                if ui.button("Save").clicked() {
                    // TODO: do this with a 'dirty' flag on AppSettings, dedup calls to settings.save()
                    settings.save()
                }
                // TODO: give a way to keep the file name as an editable value.
                // if ui.text_edit_singleline(settings.ctx().file_path).changed() {
                //     event!(Level::INFO, "file path changed");
                // }
            });
        });
        egui::SidePanel::left("side panel left").show(ctx, |ui| {
            ui.label("Side Panel");
        });

        egui::SidePanel::right("side panel right").show(ctx, |ui| {
            ui.label("Side Panel");
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
                    settings.ctx_mut().set_pitch(datastructures::PitchName::C);
                }
                if ui.input(|i| i.key_pressed(Key::D)) {
                    settings.ctx_mut().set_pitch(datastructures::PitchName::D);
                }
                if ui.input(|i| i.key_pressed(Key::E)) {
                    settings.ctx_mut().set_pitch(datastructures::PitchName::E);
                }
                if ui.input(|i| i.key_pressed(Key::F)) {
                    settings.ctx_mut().set_pitch(datastructures::PitchName::F);
                }
                if ui.input(|i| i.key_pressed(Key::G)) {
                    settings.ctx_mut().set_pitch(datastructures::PitchName::G);
                }
                if ui.input(|i| i.key_pressed(Key::A)) {
                    settings.ctx_mut().set_pitch(datastructures::PitchName::A);
                }
                if ui.input(|i| i.key_pressed(Key::B)) {
                    settings.ctx_mut().set_pitch(datastructures::PitchName::B);
                }
                // <space>: plause/play
                if ui.input(|i| i.key_pressed(Key::Space)) {
                    if sequencer_io.is_playing() {
                        sequencer_io.stop();
                    } else {
                        let end_instant = settings.ctx_mut().track.get_last_instant() as u64;
                        sequencer_io.set_track(settings.ctx_mut().track.clone());
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
                        let end_instant = settings.ctx_mut().track.get_last_instant() as u64;
                        sequencer_io.set_track(settings.ctx_mut().track.clone());
                        let start_instant = 0;
                        let is_looping = false;
                        sequencer_io.restart(start_instant, end_instant + 1, is_looping);
                    }
                }

                if ui.input(|i| i.key_pressed(Key::H)) {
                    if ui.input(|i| i.modifiers.shift || i.modifiers.command || i.modifiers.ctrl) {
                        settings.ctx_mut().lower_octave();
                    }
                    else {
                        settings.ctx_mut().cursor_move_left_one();
                    }
                }
                if ui.input(|i| i.key_pressed(Key::J)) {
                    if ui.input(|i| i.modifiers.shift || i.modifiers.command || i.modifiers.ctrl) {
                        settings.ctx_mut().increase_nsteps();
                    }
                    else {
                        settings.ctx_mut().cursor_move_down_one();
                    }
                }
                if ui.input(|i| i.key_pressed(Key::K)) {
                    if ui.input(|i| i.modifiers.shift || i.modifiers.command || i.modifiers.ctrl) {
                        settings.ctx_mut().decrease_nsteps();
                    }
                    else {
                        settings.ctx_mut().cursor_move_up_one();
                    }
                }
                if ui.input(|i| i.key_pressed(Key::L)) {
                    if ui.input(|i| i.modifiers.shift || i.modifiers.command || i.modifiers.ctrl) {
                        settings.ctx_mut().raise_octave();
                    } else {
                        settings.ctx_mut().cursor_move_right_one();
                    }
                }
                if ui.input(|i| i.key_pressed(Key::Backspace)) {
                    settings.ctx_mut().delete_line();
                }
                if ui.input(|i| i.key_pressed(Key::S) && i.modifiers.command) {
                    settings.save();
                    // save(Some(ctx), &settings.ctx());
                }
                // if ui.input(|i| i.key_pressed(Key::O) && i.modifiers.command) {
                //     if let Some(new_ctx) = open(Some(ctx), &settings.ctx()) {
                //         settings.ctx() = new_ctx;
                //         settings.current_file_path = settings.ctx().file_path.clone();
                //         settings.save();
                //     }
                // }

                if ui.input(|i| i.key_pressed(Key::Z) && i.modifiers.command) {
                    if ui.input(|i| i.modifiers.shift) {
                        settings.ctx_mut().redo_action();
                    } else {
                        settings.ctx_mut().undo_action();
                    }
                }
                if ui.input (|i| i.key_pressed(Key::Num2)) {
                    settings.ctx_mut().toggle_flat();
                }
                if ui.input (|i| i.key_pressed(Key::Num3)) {
                    settings.ctx_mut().toggle_sharp();
                }
                if ui.input (|i| i.key_pressed(Key::Enter)) {
                    settings.ctx_mut().newline();
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
                (settings.ctx_mut().selection.cursor().y *
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
            let cursor_box_top_left = logical_to_draw_min(settings.ctx_mut().selection.cursor());

            // place cursor at *end* of the box, if the box is filled.
            let cursor_loc =
                if settings.ctx().track.get_note_from_coord(settings.ctx().selection.x, settings.ctx().selection.y).is_some() {
                    cursor_box_top_left + box_dim - cursor_dim
                } else {
                    cursor_box_top_left
                };
            cursorEaser.set(cursor_loc);
            cursorEaser.damping = 0.08; cursorEaser.step();
            let cursor_loc = cursorEaser.get();


            let draw = logical_to_draw_min(Pos2::new(settings.ctx_mut().selection.x as f32, settings.ctx_mut().selection.y as f32));
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
                    if let Some(note) = settings.ctx_mut().track.get_note_from_coord(x, y) {
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
