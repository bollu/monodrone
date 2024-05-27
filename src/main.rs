#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")] // hide console window on Windows in release
#![allow(rustdoc::missing_crate_level_docs)] // it's an example

use eframe::{egui};
use egui::{ahash::{HashSetExt}};


const GOLDEN_RATIO: f32 = 1.61803398875;

use tracing_subscriber::layer::SubscriberExt;
use tracing::{event, Level};
mod monodroneffi;
mod leanffi;

mod material {
    pub const RED : egui::Color32 = egui::Color32::from_rgb(231, 111, 81);      // Red 500
    pub const BLUE : egui::Color32 = egui::Color32::from_rgb(42, 157, 143);    // Blue 500
    pub const GREEN : egui::Color32 = egui::Color32::from_rgb(233, 196, 106);    // Green 500
}


fn main() -> Result<(), eframe::Error> {

    tracing_subscriber::fmt().init();
    let _ = tracing::subscriber::set_global_default(
        tracing_subscriber::registry()
        .with(tracing_tracy::TracyLayer::default()));

    let options = eframe::NativeOptions {
        viewport: egui::ViewportBuilder::default().with_maximized(true),
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

    event!(Level::INFO, "Starting up");

    eframe::run_simple_native("Monodrone", options, move |ctx, _frame| {
;        egui::CentralPanel::default().show(ctx, |ui| {
            egui::ScrollArea::horizontal().show(ui, |ui| {
                for i in 0..32 {
                    ui.horizontal_top(|ui| {
                        let color = match i % 3 {
                            0 => material::RED,
                            1 => material::BLUE,
                            2 => material::GREEN,
                            _ => material::RED,
                        };
                        ui.painter().rect_filled(egui::Rect::from_min_size(
                            egui::Pos2::new((i * (60 + 5)) as f32, 60 as f32),
                            egui::vec2(60.0, (60 / 2) as f32 )),
                            6.0, color);
                    });
                }
                // ui.horizontal(|ui| {
                //     let name_label = ui.label("Your name: ");
                //     ui.text_edit_singleline(&mut name)
                //         .labelled_by(name_label.id);
                // });

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

                // ui.add(egui::Slider::new(&mut age, 0..=120).text("age"));
                // if ui.button("Increment").clicked() {
                //     age += 1;
                // }
            });
        });
    })
}
