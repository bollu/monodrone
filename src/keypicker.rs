use std::sync::Arc;

use crate::datastructures::*;
use egui::*;

use crate::egui_input::*;
use crate::constants::*;


impl KeySignature {
    pub fn layout_in_ui(&self, ui: &mut Ui) -> (Pos2, Arc<Galley>, Response) {
        let text = egui::WidgetText::RichText(egui::RichText::new(self.key.str_no_octave()));
        // let valign = ui.text_valign();

        let pos = pos2(ui.max_rect().left(), ui.cursor().top());
        let mut layout_job = text.into_layout_job(ui.style(), FontSelection::Default, Align::Center);
        let galley = ui.fonts(|fonts| fonts.layout_job(layout_job));
        let rect = galley.rows[0].rect.translate(vec2(pos.x, pos.y));
        let sense = Sense::hover();

        let (rect, mut response) = ui.allocate_at_least(galley.size(), sense);
        // let mut response = ui.allocate_rect(rect, sense);

        let galley_pos = match galley.job.halign {
            Align::LEFT => rect.left_top(),
            Align::Center => rect.center_top(),
            Align::RIGHT => rect.right_top(),
        };
        (galley_pos, galley, response)
    }
}

impl egui::Widget for &mut KeySignature  {
    fn ui(self, ui: &mut Ui) -> Response {

        let (galley_pos, galley, mut response) = self.layout_in_ui(ui);
        if response.hovered() {
            ui.input_mut (|i| {
                self.key = consume_pitch_modifier_key(i, self.key);
            })
        }
        // let (galley_pos, galley, mut response) = self.layout_in_ui(ui);
        // response.widget_info(|| WidgetInfo::labeled(WidgetType::Label, ui.is_enabled(), galley.text()));


        let painter = ui.painter_at(ui.available_rect_before_wrap());
        let avail_rect = ui.available_rect_before_wrap();

        let box_color = if response.hovered() {
            BOX_CURSORED_COLOR
        } else {
            BOX_DESELECTED_COLOR
        };

        let text_color = if response.hovered() {
            TEXT_COLOR_LEADING
        } else {
            TEXT_COLOR_FOLLOWING
        };

        let response_color = ui.style().visuals.text_color();
        response = response.on_hover_text(galley.text());
        ui.painter().add(
            epaint::TextShape::new(galley_pos, galley, response_color)
        );

        response
    }

}

/*
impl Label {
    /// Do layout and position the galley in the ui, without painting it or adding widget info.
    pub fn layout_in_ui(self, ui: &mut Ui) -> (Pos2, Arc<Galley>, Response) {
        let selectable = self
            .selectable
            .unwrap_or_else(|| ui.style().interaction.selectable_labels);

        let mut sense = self.sense.unwrap_or_else(|| {
            if ui.memory(|mem| mem.options.screen_reader) {
                // We only want to focus labels if the screen reader is on.
                Sense::focusable_noninteractive()
            } else {
                Sense::hover()
            }
        });

        if selectable {
            // On touch screens (e.g. mobile in `eframe` web), should
            // dragging select text, or scroll the enclosing [`ScrollArea`] (if any)?
            // Since currently copying selected text in not supported on `eframe` web,
            // we prioritize touch-scrolling:
            let allow_drag_to_select = ui.input(|i| !i.has_touch_screen());

            let mut select_sense = if allow_drag_to_select {
                Sense::click_and_drag()
            } else {
                Sense::click()
            };
            select_sense.focusable = false; // Don't move focus to labels with TAB key.

            sense = sense.union(select_sense);
        }

        if let WidgetText::Galley(galley) = self.text {
            // If the user said "use this specific galley", then just use it:
            let (rect, response) = ui.allocate_exact_size(galley.size(), sense);
            let pos = match galley.job.halign {
                Align::LEFT => rect.left_top(),
                Align::Center => rect.center_top(),
                Align::RIGHT => rect.right_top(),
            };
            return (pos, galley, response);
        }

        let valign = ui.text_valign();
        let mut layout_job = self
            .text
            .into_layout_job(ui.style(), FontSelection::Default, valign);

        let available_width = ui.available_width();

        let wrap_mode = self.wrap_mode.unwrap_or_else(|| ui.wrap_mode());
        if wrap_mode == TextWrapMode::Wrap
            && ui.layout().main_dir() == Direction::LeftToRight
            && ui.layout().main_wrap()
            && available_width.is_finite()
        {
            // On a wrapping horizontal layout we want text to start after the previous widget,
            // then continue on the line below! This will take some extra work:

            let cursor = ui.cursor();
            let first_row_indentation = available_width - ui.available_size_before_wrap().x;
            debug_assert!(first_row_indentation.is_finite());

            layout_job.wrap.max_width = available_width;
            layout_job.first_row_min_height = cursor.height();
            layout_job.halign = Align::Min;
            layout_job.justify = false;
            if let Some(first_section) = layout_job.sections.first_mut() {
                first_section.leading_space = first_row_indentation;
            }
            let galley = ui.fonts(|fonts| fonts.layout_job(layout_job));

            let pos = pos2(ui.max_rect().left(), ui.cursor().top());
            assert!(!galley.rows.is_empty(), "Galleys are never empty");
            // collect a response from many rows:
            let rect = galley.rows[0].rect.translate(vec2(pos.x, pos.y));
            let mut response = ui.allocate_rect(rect, sense);
            for row in galley.rows.iter().skip(1) {
                let rect = row.rect.translate(vec2(pos.x, pos.y));
                response |= ui.allocate_rect(rect, sense);
            }
            (pos, galley, response)
        } else {
            // Apply wrap_mode, but don't overwrite anything important
            // the user may have set manually on the layout_job:
            match wrap_mode {
                TextWrapMode::Extend => {
                    layout_job.wrap.max_width = f32::INFINITY;
                }
                TextWrapMode::Wrap => {
                    layout_job.wrap.max_width = available_width;
                }
                TextWrapMode::Truncate => {
                    layout_job.wrap.max_width = available_width;
                    layout_job.wrap.max_rows = 1;
                    layout_job.wrap.break_anywhere = true;
                }
            }

            if ui.is_grid() {
                // TODO(emilk): remove special Grid hacks like these
                layout_job.halign = Align::LEFT;
                layout_job.justify = false;
            } else {
                layout_job.halign = self.halign.unwrap_or(ui.layout().horizontal_placement());
                layout_job.justify = ui.layout().horizontal_justify();
            };

            let galley = ui.fonts(|fonts| fonts.layout_job(layout_job));
            let (rect, response) = ui.allocate_exact_size(galley.size(), sense);
            let galley_pos = match galley.job.halign {
                Align::LEFT => rect.left_top(),
                Align::Center => rect.center_top(),
                Align::RIGHT => rect.right_top(),
            };
            (galley_pos, galley, response)
        }
    }
}

impl Widget for Label {
    fn ui(self, ui: &mut Ui) -> Response {
        // Interactive = the uses asked to sense interaction.
        // We DON'T want to have the color respond just because the text is selectable;
        // the cursor is enough to communicate that.
        let interactive = self.sense.map_or(false, |sense| sense != Sense::hover());

        let selectable = self.selectable;

        let (galley_pos, galley, mut response) = self.layout_in_ui(ui);
        response
            .widget_info(|| WidgetInfo::labeled(WidgetType::Label, ui.is_enabled(), galley.text()));

        if ui.is_rect_visible(response.rect) {
            if galley.elided {
                // Show the full (non-elided) text on hover:
                response = response.on_hover_text(galley.text());
            }

            let response_color = if interactive {
                ui.style().interact(&response).text_color()
            } else {
                ui.style().visuals.text_color()
            };

            let underline = if response.has_focus() || response.highlighted() {
                Stroke::new(1.0, response_color)
            } else {
                Stroke::NONE
            };

            let selectable = selectable.unwrap_or_else(|| ui.style().interaction.selectable_labels);
            if selectable {
                LabelSelectionState::label_text_selection(
                    ui,
                    &response,
                    galley_pos,
                    galley,
                    response_color,
                    underline,
                );
            } else {
                ui.painter().add(
                    epaint::TextShape::new(galley_pos, galley, response_color)
                        .with_underline(underline),
                );
            }
        }

        response
    }
}
*/



// TODO: write this as `impl Widget for &mut KeySignature`
pub fn egui_key_signature_picker(this : &mut KeySignature, ui : &mut egui::Ui) {

    let focused = ui.memory(|mem| mem.has_focus(ui.id()));
    // consume the pitch change event.
    if focused {
        ui.input_mut (|i| {
            this.key = consume_pitch_modifier_key(i, this.key);
        })
    }
    // let (galley_pos, galley, mut response) = self.layout_in_ui(ui);
    // response.widget_info(|| WidgetInfo::labeled(WidgetType::Label, ui.is_enabled(), galley.text()));


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

    let dim = ui.available_size();
    let dim = Rect::from_min_size(Pos2::ZERO, dim.x.min(dim.y) * Vec2::splat(0.5));
    painter.rect_filled (dim,
        egui::Rounding::default().at_least(2.0),
        box_color);

    painter.text(Pos2::ZERO,
        Align2::LEFT_TOP,
        this.key.str_no_octave(),
        FontId::monospace(FONT_SIZE_NOTE),
        text_color);

}
