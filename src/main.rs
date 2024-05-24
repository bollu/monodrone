#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")] // hide console window on Windows in release
#![allow(rustdoc::missing_crate_level_docs)] // it's an example

use eframe::{egui};
use egui::{ahash::{HashSet, HashSetExt}, Pos2, Rect};


use debug_panic::debug_panic;
use tracing_subscriber::layer::SubscriberExt;
use tracing::{event, Level};
use std::collections::HashMap;

mod monodroneffi;
// 
// #[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
// enum NoteEvent {
//     Rest, // a rest, play nothing
//     Continue, // continue playing the previous note, and end if it is followed by a rest, and continue if it is followed by a continue,
//     Trigger, // trigger a new note.
// }
// 
// 
// // deriving eq, partialeq, hash, and clone for the Pitch struct.
// #[derive(Eq, PartialEq, Hash, Clone, Copy, Debug)]
// struct Pitch {
//     midi: u8 // 60 = middle C as per MIDI.
// }
// impl Pitch {
//     fn middleC() -> Pitch {
//         Pitch { midi: 60 }
//     }
//     fn from_str (s: &str) -> Option<Pitch> {
//         let midi = match s {
//             "B#" => 60, // "B#" is the same as "C"
//             "C" => 60,
//             "C#" => 61,
//             "Db" => 61, // "Db" is the same as "C#
//             "D" => 62,
//             "D#" => 63,
//             "Eb" => 63, // "Eb" is the same as "D#"
//             "E" => 64,
//             "Fb" => 64, // "Fb" is the same as "E"
//             "F" => 65,
//             "E#" => 65, // "E#" is the same as "F"
//             "F#" => 66,
//             "Gb" => 66, // "Gb" is the same as "F#"
//             "G" => 67,
//             "G#" => 68,
//             "Ab" => 68, // "Ab" is the same as "G#"
//             "A" => 69,
//             "A#" => 70,
//             "Bb" => 70, // "Bb" is the same as "A#"
//             "B" => 71,
//             "Cb" => 71, // "Cb" is the same as "B"
//             _ => return None
//         };
//         Some(Pitch { midi })
//     }
// }
// const MAX_SEQUENCER_LENGTH : usize = 1024;
// 
// 
// // a point is a pair of a pitch and an index into the sequencer at that pitch.
// type Point = (Pitch, usize);
// 
// #[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
// struct Cursor {
//     mark : Point, // location that user marked when starting to drag.
//     cur : Point // location that user is dragging around
// }
// 
// impl Cursor {
//     fn point (p : Point) -> Cursor {
//         Cursor {
//             mark : p,
//             cur : p
//         }
//     }
// }
// 
// type Cursors = Vec<Cursor>;
// 
// // logical state of the sequencer.
// struct SequencerLogic {
//     pitch2ix2event : HashMap<Pitch, [NoteEvent; MAX_SEQUENCER_LENGTH]>,
//     length : usize,
//     breaks : HashSet<usize>, // locations of breaks in the sequencer.
//     cursors : Cursors,
// }
// 
// impl SequencerLogic {
//     fn new() -> SequencerLogic {
//         let mut pitches = HashMap::new();
//         pitches.insert(Pitch::middleC(), [NoteEvent::Rest; MAX_SEQUENCER_LENGTH]);
// 
//         // we always start with middle C
//         SequencerLogic {
//             pitch2ix2event : pitches,
//             length : 1,
//             breaks : HashSet::new(),
//             cursors : vec!(Cursor::point((Pitch::middleC(), 0)))
//         }
//     }
//     
//     fn add_event(&mut self, pitch: Pitch, ix: usize, event: NoteEvent) {
//         if ix >= MAX_SEQUENCER_LENGTH {
//             panic!("Sequencer length exceeded");
//         }
//         self.pitch2ix2event.entry(pitch).or_insert([NoteEvent::Rest; MAX_SEQUENCER_LENGTH])[ix] = event;
//         self.length = self.length.max(ix + 1);
//     }
//     fn add_break(&mut self, ix: usize) {
//         if ix < self.length {
//             event!(Level::ERROR, "Added break at index {} which is less than the length of the sequencer {}", ix, self.length);
//             debug_panic!();
//         }
//     }
//     fn remove_break(&mut self, ix: usize) {
//         self.breaks.remove(&ix);
//     }
//     fn get_event(&self, pitch: Pitch, ix: usize) -> NoteEvent {
//         if ix >= self.length {
//             panic!("Index out of bounds");
//         }
//         // if pitch exists, then return the event, otherwise return a rest.
//         self.pitch2ix2event.get(&pitch).map_or(NoteEvent::Rest, |events| events[ix])
//     }
// 
// }

// struct SequencerRender {

// }

// impl SequencerRender {
//     const CELL_WIDTH : f32 = 20.0;
//     const CELL_HEIGHT : f32 = 8.0;

//     fn new() -> SequencerRender {
//         SequencerRender {}
//     }
// }

// struct AppState {
//     sequencerLogic : SequencerLogic,
//     sequencerRender : SequencerRender,
// }

// // draw the current state.
// fn draw() {

// }


mod material {
    pub const RED : egui::Color32 = egui::Color32::from_rgb(244, 67, 54);      // Red 500
    pub const BLUE : egui::Color32 = egui::Color32::from_rgb(33, 150, 243);    // Blue 500
    pub const GREEN : egui::Color32 = egui::Color32::from_rgb(76, 175, 80);    // Green 500
}

fn main() -> Result<(), eframe::Error> {
    let mut monodrone_ctx = unsafe { monodroneffi::new_context(); }; 
    // let app_state : AppState = AppState {
    //     sequencerLogic : SequencerLogic::new(),
    //     sequencerRender : SequencerRender::new(),
    // };


    // tracing_subscriber::fmt().init();
    let _ = tracing::subscriber::set_global_default(
        tracing_subscriber::registry()
        .with(tracing_tracy::TracyLayer::default()));

    let options = eframe::NativeOptions {
        viewport: egui::ViewportBuilder::default().with_inner_size([320.0, 240.0]),
        ..Default::default()
    };
    
    event!(Level::INFO, "Starting up");

    // Our application state:
    let mut name = "Arthur".to_owned();
    let mut age = 42;

    eframe::run_simple_native("My egui App", options, move |ctx, _frame| {
        egui::CentralPanel::default().show(ctx, |ui| {
            egui::ScrollArea::vertical().show(ui, |ui| {
                ui.heading("My egui Application");
                ui.horizontal(|ui| {
                    let name_label = ui.label("Your name: ");
                    ui.text_edit_singleline(&mut name)
                        .labelled_by(name_label.id);
                });
                event!(Level::INFO, "XX");

                // for (i, event) in app_state.sequencerLogic.pitch2ix2event.iter() {
                //     event!(Level::INFO, "Drawing pitch {:?}", i);
                //     ui.horizontal(|ui| {
                //         ui.label(format!("{:?}", i));
                //         for (j, e) in event.iter().enumerate() {
                //             let color = match e {
                //                 NoteEvent::Rest => material::RED,
                //                 NoteEvent::Continue => material::BLUE,
                //                 NoteEvent::Trigger => material::GREEN,
                //             };
                //             ui.painter().rect_filled(Rect::from_min_size(Pos2::new(i.midi as f32 * SequencerRender::CELL_WIDTH, j as f32 * SequencerRender::CELL_HEIGHT), egui::vec2(SequencerRender::CELL_WIDTH, SequencerRender::CELL_HEIGHT)), 0.0, color);
                //         }
                //     });
                // }

                ui.add(egui::Slider::new(&mut age, 0..=120).text("age"));
                if ui.button("Increment").clicked() {
                    age += 1;
                }
            });
        });
    })
}
