#![allow(rustdoc::missing_crate_level_docs)] // it's an example
#![allow(dead_code)]

use chords::NoteGroup;
use egui::Key;



 // 0.7.2










use eframe::egui;
use egui::*;


// const GOLDEN_RATIO: f32 = 1.618_034;








use crate::{*, MidiSequencerIO};
use crate::ideimage::*;
use crate::constants::*;

// state of the editor UI
pub struct EditorUIState {
    debounce_movement : Debouncer,
    debounce_undo : Debouncer,
    camera_easer : Easer<egui::Vec2>,
    now_playing_easer : Easer<egui::Pos2>,
    cursor_easer : Easer<egui::Pos2>,
}

impl EditorUIState {

    pub fn new() -> EditorUIState {
        let debounce_movement = Debouncer::new(80.0 / 1000.0);
        let debounce_undo = Debouncer::new(150.0 / 1000.0);

        let camera_easer = Easer::new(Vec2::ZERO);
        let now_playing_easer = Easer::new(Pos2::ZERO);
        let cursor_easer = Easer::new(Pos2::ZERO);
        EditorUIState {
            debounce_movement,
            debounce_undo,
            camera_easer,
            now_playing_easer,
            cursor_easer,
        }
    }
}

pub fn egui_editor(this : &mut EditorUIState, settings : &mut IDEImage, sequencer_io : &mut MidiSequencerIO, ctx : &egui::Context, ui : &mut egui::Ui) {
    // return;
    // let time_elapsed = rl.get_frame_time();
    let time_elapsed = 0.01; // TODO: fix this!
    this.debounce_movement.add_time_elapsed(time_elapsed);
    this.debounce_undo.add_time_elapsed(time_elapsed);


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
            settings.ctx_mut().set_pitch(PitchName::C);
        }
        if ui.input(|i| i.key_pressed(Key::D)) {
            settings.ctx_mut().set_pitch(PitchName::D);
        }
        if ui.input(|i| i.key_pressed(Key::E)) {
            settings.ctx_mut().set_pitch(PitchName::E);
        }
        if ui.input(|i| i.key_pressed(Key::F)) {
            settings.ctx_mut().set_pitch(PitchName::F);
        }
        if ui.input(|i| i.key_pressed(Key::G)) {
            settings.ctx_mut().set_pitch(PitchName::G);
        }
        if ui.input(|i| i.key_pressed(Key::A)) {
            settings.ctx_mut().set_pitch(PitchName::A);
        }
        if ui.input(|i| i.key_pressed(Key::B)) {
            settings.ctx_mut().set_pitch(PitchName::B);
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

    let painter = ui.painter_at(ui.available_rect_before_wrap());
    let avail_rect = ui.available_rect_before_wrap();

    this.camera_easer.set(Vec2::new(0.,
        (settings.ctx_mut().selection.cursor().y *
            (BOX_DIM.y + BOX_PADDING_MIN.y + BOX_PADDING_MAX.y) - avail_rect.height() * 0.5).max(0.0))
    );
    this.camera_easer.step();


    let logical_to_sidebar_text_min = |logical: egui::Pos2| -> egui::Pos2 {
        avail_rect.min + WINDOW_PADDING +
        logical.to_vec2() * (BOX_DIM + BOX_PADDING_MIN + BOX_PADDING_MAX) - this.camera_easer.get()
    };

    // now playing.
    let logical_to_draw_min = |logical: egui::Pos2| -> egui::Pos2 {
        avail_rect.min + WINDOW_PADDING + Vec2::new(SIDEBAR_LEFT_WIDTH, 0.0) +
        logical.to_vec2() * (BOX_DIM + BOX_PADDING_MIN + BOX_PADDING_MAX) - this.camera_easer.get()
    };


    {
        let cur_instant = sequencer_io.sequencer.lock().as_ref().unwrap().cur_instant;
        let now_playing_box_y : i32 = cur_instant as i32 - 1;
        this.now_playing_easer.set(logical_to_draw_min(Pos2::new(0., now_playing_box_y as f32)));
        this.now_playing_easer.step();
    }

    for x in 0u64..NTRACKS {
        for y in 0u64..TRACK_LENGTH {
            let draw = logical_to_draw_min(Pos2::new(x as f32, y as f32));
            painter.rect_filled (Rect::from_min_size(draw, BOX_DIM),
                egui::Rounding::default().at_least(2.0),
                BOX_DESELECTED_COLOR);
        }
    }

    // TODO: for the love of got, clean this up.
    let cursor_dim = BOX_DIM * Vec2::new(1., 0.2);
    let cursor_box_top_left = logical_to_draw_min(settings.ctx_mut().selection.cursor());

    // place cursor at *end* of the box, if the box is filled.
    let cursor_loc =
        if settings.ctx().track.get_note_from_coord(settings.ctx().selection.x, settings.ctx().selection.y).is_some() {
            cursor_box_top_left + BOX_DIM - cursor_dim
        } else {
            cursor_box_top_left
        };
    this.cursor_easer.set(cursor_loc);
    this.cursor_easer.damping = 0.2; this.cursor_easer.step();
    let cursor_loc = this.cursor_easer.get();


    let draw = logical_to_draw_min(Pos2::new(settings.ctx_mut().selection.x as f32, settings.ctx_mut().selection.y as f32));
    painter.rect_filled (Rect::from_min_size(draw, BOX_DIM),
        egui::Rounding::default().at_least(2.0),
        BOX_CURSORED_COLOR);

    painter.rect_filled (Rect::from_min_size(cursor_loc, cursor_dim),
        Rounding::default().at_least(2.0),
        BOX_CURSOR_COLOR);

    for y in 0u64..TRACK_LENGTH {
        let draw = logical_to_sidebar_text_min(Pos2::new(0f32, y as f32));
        painter.text(draw, Align2::LEFT_TOP, &format!("{:02}", y), FontId::monospace(FONT_SIZE_NOTE), TEXT_COLOR_FOLLOWING);
    }

    for x in 0u64..NTRACKS {
        for y in 0u64..TRACK_LENGTH {
            let draw = logical_to_draw_min(Pos2::new(x as f32, y as f32));
            if let Some(note) = settings.ctx_mut().track.get_note_from_coord(x, y) {
                let text_color = if note.x == x && note.y() == y {
                    TEXT_COLOR_LEADING
                } else {
                    TEXT_COLOR_FOLLOWING
                };

                let note_text_padding = Vec2::splat(5.0);
                painter.text(draw + note_text_padding,
                    Align2::LEFT_TOP, note.str(), FontId::monospace(FONT_SIZE_NOTE), text_color);
                let octave_text_padding = Vec2::new(2., 2.);
                let octave_text_color = egui::Color32::from_rgb(104, 159, 56);
                let octave_text = painter.layout_no_wrap(note.pitch.octave.to_string(),
                    FontId::monospace(FONT_SIZE_OCTAVE), octave_text_color);
                let text_pos = draw + BOX_DIM - octave_text_padding - octave_text.rect.size();
                painter.galley(text_pos, octave_text, octave_text_color);
            };
        }
    }

    painter.rect_filled (Rect::from_min_size(this.now_playing_easer.get(),
        BOX_DIM * Vec2::new(0.1, 1.0)),
        Rounding::default().at_least(4.0),
        BOX_NOW_PLAYING_COLOR);

    for y in 0u64..TRACK_LENGTH {
        let ng = settings.ctx_mut().chord_info.get(y);
        let text = match ng {
            NoteGroup::Chord(cs) => {
                if cs.is_empty() {
                    "?".to_string()
                } else {
                    let chord = cs.first().unwrap();
                    chord.to_string()
                }
            }
            NoteGroup::Two(i) => i.string(),
            NoteGroup::Single(p) => p.name.str().to_string(),
            NoteGroup::Empty => "".to_string(),
        };
        painter.text(logical_to_draw_min(pos2(NTRACKS as f32, y as f32)),
            Align2::LEFT_TOP, text, FontId::monospace(FONT_SIZE_NOTE), TEXT_COLOR_LEADING);
        let _octave_text_padding = Vec2::new(2., 2.);
        let _octave_text_color = egui::Color32::from_rgb(104, 159, 56);
    }

    if !focused {
        painter.rect_filled(ui.max_rect(), Rounding::default(),
            Color32::from_black_alpha(150));
    }
    ctx.request_repaint();
}
