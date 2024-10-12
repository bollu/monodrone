use egui::*;
use crate::datastructures::*;


// consume a key press of a pitch.
pub fn consume_pitch_name_key_press(i : &mut egui::InputState) -> Option<PitchName> {
    if i.consume_key(Modifiers::NONE, Key::C) {
        Some(PitchName::C)
    } else if i.consume_key(Modifiers::NONE, Key::D) {
        Some(PitchName::D)
    } else if i.consume_key(Modifiers::NONE, Key::E) {
        Some(PitchName::E)
    } else if i.consume_key(Modifiers::NONE, Key::F) {
        Some(PitchName::F)
    } else if i.consume_key(Modifiers::NONE, Key::G) {
        Some(PitchName::G)
    } else if i.consume_key(Modifiers::NONE, Key::A) {
        Some(PitchName::A)
    } else if i.consume_key(Modifiers::NONE, Key::B) {
        Some(PitchName::B)
    } else {
        None
    }
}

// consume a key press of an accidental.
pub fn consume_accidental_key_press(i : &mut egui::InputState) -> Option<Accidental> {
    if i.consume_key(Modifiers::NONE, Key::Num2) {
        Some(Accidental::Flat)
    } else if i.consume_key(Modifiers::NONE, Key::Num3) {
        Some(Accidental::Sharp)
    }else {
        None
    }

}

// Build a component that toggles a value.
// If the old accidental is the new accidental, then we toggle it.
// Otherwise, we set it to the new accidental.
pub fn toggle_accidental(old : Accidental, new : Accidental) -> Accidental {
    if old == new {
        Accidental::Natural
    } else {
        new
    }
}

pub fn consume_pitch_modifier_key(i : &mut egui::InputState, pitch : Pitch) -> Pitch {
    let mut pitch = pitch.clone();
    if let Some(pitch_name) = consume_pitch_name_key_press(i) {
        pitch.name = pitch_name;
    }

    if let Some(accidental) = consume_accidental_key_press(i) {
        pitch.accidental = toggle_accidental(pitch.accidental, accidental);
    }
    return pitch;
}
