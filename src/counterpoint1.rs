// This is two voice counterpoint.
use crate::{datastructures::{Pitch}, PlayerTrack};
use crate::constants::{TRACK_LENGTH};

// list the errors in counterpoint from Fux's book:
#[derive(Debug, PartialEq, PartialOrd, Clone)]
// TODO: replace with IntervalKind from Chord.
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
    pub fn assonance_for(p : Pitch, q: Pitch) -> AssonanceKind {
        if (p.pitch() - q.pitch()) % num_semitones_in_octave() == 0 {
            AssonanceKind::PerfectFifthConsonance
        } else if (p.pitch() - q.pitch()) % num_semitones_in_fifth() == 0 {
            AssonanceKind::PerfectFifthConsonance
        } else{
            AssonanceKind::Dissonance
        }

    }

    pub fn is_perfect(&self) -> bool {
        match self {
            AssonanceKind::PerfectOctaveConsonance => true,
            AssonanceKind::PerfectFifthConsonance => true,
            _ => false,
        }
    }
}

#[derive(Debug, PartialEq, PartialOrd, Clone)]
enum Motion {
    Parallel,
    Similar,
    Contrary,
    Oblique
}

impl Motion {
    pub fn motion_for(ps : (Pitch, Pitch), qs: (Pitch, Pitch)) -> Motion {
        let p1 = ps.0.pitch();
        let p2 = ps.1.pitch();
        let q1 = qs.0.pitch();
        let q2 = qs.1.pitch();
        // move in the same direction.
        let dp = p2 - p1;
        let dq = q2 - q1;


        // neither moves.
        if dp == 0 && dq == 0 {
            return Motion::Parallel;
        }

        // only one moves.
        if dp == 0 || dq == 0 {
            return Motion::Oblique;
        }

        // both move.
        assert!(dp != 0);
        assert!(dq != 0);

        if dp * dq >= 0 {
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


#[derive(Debug, PartialEq, PartialOrd, Clone)]
pub enum LintKind {
    ParallelPerfectConsonance,
}

// counterpoint lints.
#[derive(Debug, PartialEq, PartialOrd, Clone)]
pub struct Lint {
    pub kind : LintKind,
    pub loc_start : (i32, i32), // (x, y)
    pub num_notes : i32,
}


#[derive(Debug, PartialEq, PartialOrd, Clone)]
#[derive(Default)]
pub struct CounterpointLints {
    lints : Vec<Lint>,
}



// Countrapunctal information for a track.
impl CounterpointLints {
    pub fn from_track(track: &PlayerTrack) -> CounterpointLints {
        let mut lints : CounterpointLints = Default::default();
        for i in 0..TRACK_LENGTH-1 {
            // cantus firmus
            let p = match track.get_note_from_coord(0, i) {
                    Some(p) => p,
                    None => continue,
                };
            let pnext = match track.get_note_from_coord(0, i+1) {
                    Some(p) => p,
                    None => continue,
                };
            let q = match track.get_note_from_coord(0, i) {
                    Some(q) => q,
                    None => continue,
            };
            let qnext = match track.get_note_from_coord(0, i+1) {
                    Some(q) => q,
                    None => continue,
            };

            let assonance = AssonanceKind::assonance_for(pnext.pitch, qnext.pitch);
            let motion = Motion::motion_for((p.pitch, q.pitch), (pnext.pitch, qnext.pitch));

            if assonance.is_perfect() && motion == Motion::Parallel {
                let lint = Lint {
                    kind : LintKind::ParallelPerfectConsonance,
                    loc_start : (0, i as i32),
                    num_notes : 1,
                };

                lints.lints.push(lint);
            }
        }
        lints
    }
}
