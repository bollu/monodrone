use crate::datastructures::*;
use egui::*;

use crate::egui_input::*;
use crate::constants::*;

pub struct KeyPicker {
    pub key : Pitch,
}


fn egui_key_picker(this : &mut KeyPicker, ui : &mut egui::Ui) {

    let focused = ui.memory(|mem| mem.has_focus(ui.id()));
    // consume the pitch change event.
    if focused {
        ui.input_mut (|i| {
            this.key = consume_pitch_modifier_key(i, this.key);
        })
    }


    let painter = ui.painter_at(ui.available_rect_before_wrap());
    let avail_rect = ui.available_rect_before_wrap();

    let box_color = if focused {
        BOX_CURSORED_COLOR
    } else {
        BOX_DESELECTED_COLOR
    };

    let text_color = if focused {
        TEXT_COLOR_LEADING
    } else {
        TEXT_COLOR_FOLLOWING
    };

    painter.rect_filled (Rect::from_min_size(Pos2::ZERO, BOX_DIM),
        egui::Rounding::default().at_least(2.0),
        box_color);

    painter.text(Pos2::ZERO,
        Align2::LEFT_TOP,
        this.key.str_no_octave(),
        FontId::monospace(FONT_SIZE_NOTE),
        text_color);

}
