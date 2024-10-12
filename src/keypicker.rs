

use crate::datastructures::*;
use egui::*;

use crate::egui_input::*;



impl egui::Widget for &mut KeySignature  {
    fn ui(self, ui: &mut Ui) -> Response {
        let response = ui.label("Key signature");
        let response = response | ui.label(
            RichText::new(format!("{:^6}",self.key.str_no_octave())).monospace());
        if response.hovered() {
            ui.input_mut (|i| {
                self.key = consume_pitch_modifier_key(i, self.key);
            });
        }
        response
    }
}
