#![allow(rustdoc::missing_crate_level_docs)] // it's an example
#![allow(dead_code)]

use chords::NoteGroup;
use egui::Key;
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


use midi::*;
use datastructures::*;
use opz::*;
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


    let mut debounce_movement = Debouncer::new(80.0 / 1000.0);
    let mut debounce_undo = Debouncer::new(150.0 / 1000.0);

    let mut camera_easer = Easer::new(Vec2::ZERO);
    let mut now_playing_easer = Easer::new(Pos2::ZERO);
    let mut cursor_easer = Easer::new(Pos2::ZERO);

    now_playing_easer.damping = 0.1;


    let _ = eframe::run_simple_native(format!("monodrone({})", settings.ctx_mut().track_name).as_str(),
        options, move |ctx, _frame| {

        settings.save();

        egui::TopBottomPanel::bottom("Configuration").show(ctx, |ui| {
            // TODO: move into ide_image?
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
                    settings.new();
                }
            });
        });

        egui::SidePanel::right("Projects").show(ctx, |ui| {
            egui_project_picker(&ctx, ui, &mut settings);
        });
        egui::CentralPanel::default().show(ctx, |ui| {
            let time_elapsed = 0.01; // TODO: fix this!
            debounce_movement.add_time_elapsed(time_elapsed);
            debounce_undo.add_time_elapsed(time_elapsed);


            // TODO: refactor into a widget that requests focus.
            ctx.memory_mut(|mem| {
                mem.interested_in_focus(ui.id());
                if mem.focused().is_none() {
                    mem.request_focus(ui.id());
                }
            });
            let focused = ctx.memory(|mem| mem.has_focus(ui.id()));
            if focused { //response.hovered() {
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
                        let end_instant = settings.ctx_mut().track.get_last_instant();
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
                        let end_instant = settings.ctx_mut().track.get_last_instant();
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

            camera_easer.set(Vec2::new(0.,
                (settings.ctx_mut().selection.cursor().y *
                    (box_dim.y + box_padding_min.y + box_padding_max.y) - avail_rect.height() * 0.5).max(0.0))
            );
            camera_easer.step();



            let logical_to_sidebar_text_min = |logical: egui::Pos2| -> egui::Pos2 {
                avail_rect.min + window_padding +
                logical.to_vec2() * (box_dim + box_padding_min + box_padding_max) - camera_easer.get()
            };

            // now playing.
            let logical_to_draw_min = |logical: egui::Pos2| -> egui::Pos2 {
                avail_rect.min + window_padding + Vec2::new(sidebar_left_width, 0.0) +
                logical.to_vec2() * (box_dim + box_padding_min + box_padding_max) - camera_easer.get()
            };


            {
                let cur_instant = sequencer_io.sequencer.lock().as_ref().unwrap().cur_instant;
                let now_playing_box_y : i32 = cur_instant as i32 - 1;
                now_playing_easer.set(logical_to_draw_min(Pos2::new(0., now_playing_box_y as f32)));
                now_playing_easer.step();
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
            cursor_easer.set(cursor_loc);
            cursor_easer.damping = 0.2; cursor_easer.step();
            let cursor_loc = cursor_easer.get();


            let draw = logical_to_draw_min(Pos2::new(settings.ctx_mut().selection.x as f32, settings.ctx_mut().selection.y as f32));
            painter.rect_filled (Rect::from_min_size(draw, box_dim),
                egui::Rounding::default().at_least(2.0),
                box_cursored_color);

            painter.rect_filled (Rect::from_min_size(cursor_loc, cursor_dim),
                Rounding::default().at_least(2.0),
                box_cursor_color);

            for y in 0u64..TRACK_LENGTH {
                let draw = logical_to_sidebar_text_min(Pos2::new(0f32, y as f32));
                painter.text(draw, Align2::LEFT_TOP, &format!("{:02}", y), FontId::monospace(font_size_note), text_color_following);
            }

            for x in 0u64..NTRACKS {
                for y in 0u64..TRACK_LENGTH {
                    let draw = logical_to_draw_min(Pos2::new(x as f32, y as f32));
                    if let Some(note) = settings.ctx_mut().track.get_note_from_coord(x, y) {
                        let text_color = if note.x == x && note.y() == y {
                            text_color_leading
                        } else {
                            text_color_following
                        };

                        let note_text_padding = Vec2::splat(5.0);
                        painter.text(draw + note_text_padding,
                            Align2::LEFT_TOP, note.str(), FontId::monospace(font_size_note), text_color);
                        let octave_text_padding = Vec2::new(2., 2.);
                        let octave_text_color = egui::Color32::from_rgb(104, 159, 56);
                        let octave_text = painter.layout_no_wrap(note.pitch.octave.to_string(),
                            FontId::monospace(font_size_octave), octave_text_color);
                        let text_pos = draw + box_dim - octave_text_padding - octave_text.rect.size();
                        painter.galley(text_pos, octave_text, octave_text_color);
                    };
                }
            }

            painter.rect_filled (Rect::from_min_size(now_playing_easer.get(),
                box_dim * Vec2::new(0.1, 1.0)),
                Rounding::default().at_least(4.0),
                box_now_playing_color);

            for y in 0u64..TRACK_LENGTH {
                let ng = settings.ctx_mut().chord_info.get(y);
                let text = match ng {
                    NoteGroup::Unknown => "?".to_string(),
                    NoteGroup::Three(c) => c.string(),
                    NoteGroup::Four(c) => c.string(),
                    NoteGroup::Two(i) => i.string(),
                    NoteGroup::Single(p) => p.name.str().to_string(),
                    NoteGroup::None => "".to_string()
                };
                painter.text(logical_to_draw_min(pos2(NTRACKS as f32, y as f32)),
                    Align2::LEFT_TOP, text, FontId::monospace(font_size_note), text_color_leading);
                let octave_text_padding = Vec2::new(2., 2.);
                let octave_text_color = egui::Color32::from_rgb(104, 159, 56);
            }

            if !focused {
                painter.rect_filled(ui.max_rect(), Rounding::default(),
                    Color32::from_black_alpha(150));
            }
            ctx.request_repaint();
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
