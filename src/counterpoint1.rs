// This is two voice counterpoint.
use crate::datastructures::{PlayerNote, ui_pitch_to_midi_pitch};

// list the errors in counterpoint from Fux's book:
enum AssonanceKind {
    PerfectOctaveConsonance,
    PerfectFifthConsonance,
    ImperfectConsonance,
    Dissonance,
    PerfectFourth // now it depends on whether it's the lower or upper voice.
}

pub fn num_semitones_in_octave() -> i64 {
    12
}

pub fn num_semitones_in_fifth() -> i64 {
    7
}

impl AssonanceKind {
    // with p as the lower voice and q as the higher voice, what is the assonance?
    pub fn assonance_for(p : PlayerNote, q: PlayerNote) -> AssonanceKind {
        let p1 = ui_pitch_to_midi_pitch(p.pitch_name, p.accidental, p.octave) as i64;
        let p2 = ui_pitch_to_midi_pitch(p.pitch_name, p.accidental, p.octave) as i64;
        if p1 - p2 % num_semitones_in_octave() == 0 {
            AssonanceKind::PerfectFifthConsonance
        } else if (p1 - p2) % num_semitones_in_fifth() == 0 {
            AssonanceKind::PerfectFifthConsonance
        } else{
            AssonanceKind::Dissonance
        }

    }
}

enum Motion {
    Parallel,
    Similar,
    Contrary,
    Oblique
}

impl Motion {
    pub fn motion_for(ps : (PlayerNote, PlayerNote), qs: (PlayerNote, PlayerNote)) -> Motion {
        let p1 = ui_pitch_to_midi_pitch(ps.0.pitch_name, ps.0.accidental, ps.0.octave) as i64;
        let p2 = ui_pitch_to_midi_pitch(ps.1.pitch_name, ps.1.accidental, ps.1.octave) as i64;
        let q1 = ui_pitch_to_midi_pitch(qs.0.pitch_name, qs.0.accidental, qs.0.octave) as i64;
        let q2 = ui_pitch_to_midi_pitch(qs.1.pitch_name, qs.1.accidental, qs.1.octave) as i64;
        // move in the same direction.
        let dp = p2 - p1;
        let dq = q2 - q1;


        // neither moves.
        if (dp == 0 && dq == 0) {
            return Motion::Parallel;
        }

        // only one moves.
        if (dp == 0 || dq == 0) {
            return Motion::Oblique;
        }

        // both move.
        assert!(dp != 0);
        assert!(dq != 0);

        return if dp * dq >= 0 {
            // both in same direction
            if dp == dq {
                // and both in same distance.
                Motion::Parallel
            } else {
                Motion::Similar
            }
        } else {
            // move in opposite directions.
            Motion::Contrary
        }
    }
}
