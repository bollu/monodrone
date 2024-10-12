#![allow(rustdoc::missing_crate_level_docs)] // it's an example
#![allow(dead_code)]



use std::sync::Arc;
use tinyaudio::OutputDeviceParameters;
use eframe::egui;
use egui::*;
use rustysynth::SoundFont;
use tracing::{event, Level};
use tracing_subscriber::layer::SubscriberExt;

mod datastructures;
mod midi;
mod counterpoint1;
mod chords;
mod opz;
mod editor;
mod ideimage;
mod keypicker;
mod constants;
mod egui_input;


use midi::*;
use datastructures::*;
use editor::*;
use ideimage::*;


fn main_loop() {
    // Load the SoundFont.
    let sf2 = include_bytes!("../resources/TimGM6mb.sf2");
    let mut sf2_cursor = std::io::Cursor::new(sf2);
    let sound_font = Arc::new(SoundFont::new(&mut sf2_cursor).unwrap());

    let params = OutputDeviceParameters {
        channels_count: 2,
        sample_rate: 44100,
        channel_sample_count: 4410,
    };

    // Create the MIDI sequencer to let us send our MIDI events to the synthesizer,
    // via the sequencer that takes a sequence of MIDI events and plays them back.
    let mut sequencer_io: MidiSequencerIO = MidiSequencerIO::new(sound_font, params);

    let options = eframe::NativeOptions {
        viewport: egui::ViewportBuilder::default()
            .with_maximized(true)
            .with_icon(eframe::icon_data::from_png_bytes(include_bytes!("../favicon.png")).unwrap()),
        ..Default::default()
    };
    let mut ide_image = IDEImage::load();
    let mut editor_ui_state = EditorUIState::new();

    let _ = eframe::run_simple_native("monodrone",
        options, move |ctx, _frame| {

        ide_image.save();

        egui::TopBottomPanel::bottom("Configuration").show(ctx, |ui| {
            // TODO: move into ide_image?
            ui.with_layout(Layout::left_to_right(Align::Center), |ui| {
                ui.add(&mut ide_image.ctx_mut().key_signature);

                ui.label("Playback Speed");
                if ui.add(egui::DragValue::new(&mut ide_image.ctx_mut().playback_speed)
                    .clamp_range(0.01..=3.0)
                    .update_while_editing(false)
                    .speed(0.05)).changed() {
                    sequencer_io.set_playback_speed(ide_image.ctx_mut().playback_speed as f32);
                    event!(Level::INFO, "new Playback speed: {:?}",
                        ide_image.ctx_mut().playback_speed);
                }
                ui.label("Time Signature");
                ui.add(egui::DragValue::new(&mut ide_image.ctx_mut().time_signature.0)
                    .clamp_range(1..=9).update_while_editing(false));
                ui.label("/");
                ui.add(egui::DragValue::new(&mut ide_image.ctx_mut().time_signature.1)
                    .clamp_range(1..=9).update_while_editing(false));
                ui.label("Artist");
                ui.text_edit_singleline(&mut ide_image.ctx_mut().artist_name);
                ui.label("Title");
                ui.text_edit_singleline(&mut ide_image.ctx_mut().track_name);


            });
        });

        egui::TopBottomPanel::top("top bar").show(ctx, |ui| {
            egui::menu::bar(ui, |ui| {
                if ui.button("New").clicked() {
                    ide_image.new();
                }
            });
        });

        egui::SidePanel::right("Projects").show(ctx, |ui| {
            egui_project_picker(ctx, ui, &mut ide_image);
        });

        egui::CentralPanel::default().show(ctx, |ui| {
            egui_editor(&mut editor_ui_state,
                &mut ide_image, &mut sequencer_io, ctx, ui);
        });
    });

}

fn main() {
    tracing_subscriber::fmt().init();
    let _ = tracing::subscriber::set_global_default(
        tracing_subscriber::registry().with(tracing_tracy::TracyLayer::default()),
    );
    // testMidiInOpZ();

    // let mut opz = Opz::new();
    // opz.find_port();
    main_loop();
}
