#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")] // hide console window on Windows in release
#![allow(rustdoc::missing_crate_level_docs)] // it's an example

use std::{fs::File, sync::Arc};

use midi::Message::Start;
use raylib::prelude::*;
use tinyaudio::{run_output_device, OutputDeviceParameters};
use tinyaudio::prelude::*;

const GOLDEN_RATIO: f32 = 1.61803398875;

use rustysynth::{MidiFile, MidiFileSequencer, SoundFont, Synthesizer, SynthesizerSettings};
use tracing_subscriber::layer::SubscriberExt;
use tracing::{event, Level};
mod monodroneffi;
mod leanffi;

// mod material {
//     pub const RED : egui::Color32 = egui::Color32::from_rgb(231, 111, 81);      // Red 500
//     pub const BLUE : egui::Color32 = egui::Color32::from_rgb(42, 157, 143);    // Blue 500
//     pub const GREEN : egui::Color32 = egui::Color32::from_rgb(233, 196, 106);    // Green 500
// }


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
    let monodrone_ctx = monodroneffi::new_context();
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
    let mut synthesizer = Synthesizer::new(&sound_font, &settings).unwrap();
    // Play some notes (middle C, E, G).
    synthesizer.note_on(0, 60, 100);
    synthesizer.note_on(0, 64, 100);
    synthesizer.note_on(0, 67, 100);


    // The output buffer (3 seconds).
    let mut left: Vec<f32> = vec![0_f32; params.channel_sample_count];
    let mut right: Vec<f32> = vec![0_f32; params.channel_sample_count];


    // Start the audio output.
    let _device = run_output_device(params, {
        move |data| {
            // Render the waveform.
            synthesizer.render(&mut left[..], &mut right[..]);
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

    // Wait for 10 seconds.
    std::thread::sleep(std::time::Duration::from_secs(3));

    event!(Level::INFO, "Starting up");
    let (mut rl, thread) = raylib::init()
        .size(640, 480)
        .title("Hello, World")
        .build();


    while !rl.window_should_close() {
        let track = monodroneffi::get_track(monodrone_ctx);
        event!(Level::INFO, "track: {:?}", track);
        let mut d = rl.begin_drawing(&thread);

        d.clear_background(Color::new(50, 50, 60, 255));

        // draw tracker.
        for y in 0..100 {
            let h = 1;
            d.draw_rectangle(4, 44 * y, 100, 40 * h, Color::GRAY);
            // d.draw_rectangle_lines(10, 40 * y, 100, 40 * h, Color::DARKGRAY);
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


// fn main() -> Result<(), eframe::Error> {
//
//     tracing_subscriber::fmt().init();
//     let _ = tracing::subscriber::set_global_default(
//         tracing_subscriber::registry()
//         .with(tracing_tracy::TracyLayer::default()));
//
//     let options = eframe::NativeOptions {
//         // viewport: egui::ViewportBuilder::default().with_maximized(true),
//         // .with_fullscreen(true),
//         ..Default::default()
//     };
//
//     unsafe {
//         event!(Level::INFO, "initializing lean runtime module");
//         leanffi::lean_initialize_runtime_module();
//
//         event!(Level::INFO, "initializing monodrone");
//         monodroneffi::initialize();
//
//         event!(Level::INFO, "done with Lean initialization. Marking end of initialization.");
//         leanffi::lean_io_mark_end_initialization();
//     }
//
//     event!(Level::INFO, "creating context");
//     let monodrone_ctx = monodroneffi::new_context();
//     event!(Level::INFO, "ctx: {:p}", monodrone_ctx);
//     event!(Level::INFO, "track: {:?}", track);
//
//     event!(Level::INFO, "Starting up");
//
//     eframe::run_simple_native("Monodrone", options, move |ctx, _frame| {
//         egui::CentralPanel::default().show(ctx, |ui| {
//             egui::ScrollArea::both().scroll_bar_visibility(ScrollBarVisibility::AlwaysVisible).show(ui, |ui| {
//                 for i in 0..32 {
//                     ui.horizontal_top(|ui| {
//                         let color = match i % 3 {
//                             0 => material::RED,
//                             1 => material::BLUE,
//                             2 => material::GREEN,
//                             _ => material::RED,
//                         };
//
//                         ui.painter().rect_filled(egui::Rect::from_min_size(
//                             egui::Pos2::new(60 as f32, (i * (60 + 5)) as f32),
//                             egui::vec2(120 as f32, (60 - 10) as f32)),
//                             6.0, color);
//                     });
//                 }
//             });
//         });
//     })
// }
