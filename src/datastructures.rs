
use serde::{Serialize, Deserialize};
use core::fmt;
use std::time::SystemTime;
use std::collections::HashMap;
use tracing::{event, Level};

use crate::counterpoint1::CounterpointLints;
use crate::midi::track_get_note_events_at_time;
use crate::chords::*;
use crate::constants::*;

#[derive(Debug, Clone, Copy, PartialEq)]
// TODO: read midi
pub struct Debouncer {
    time_to_next_event: f32,
    debounce_time_sec: f32,
}

impl Debouncer {
    pub fn new(debounce_time_sec: f32) -> Self {
        Self {
            time_to_next_event: 0.0,
            debounce_time_sec,
        }
    }

    pub fn add_time_elapsed(&mut self, time_elapsed: f32) {
        self.time_to_next_event += time_elapsed;
    }

    pub fn debounce(&mut self, val: bool) -> bool {
        let out = val && (self.time_to_next_event > self.debounce_time_sec);
        if out { self.time_to_next_event = 0.0; }
        out
    }
}

pub struct Easer<T> where {
    pub target: T,
    cur: T,
    pub damping: f32,
}

impl<T, D> Easer<T>
where
    D : Copy + std::ops::Mul<f32, Output = D>, // delta
    T: Copy + std::ops::Add<D, Output = T> + std::ops::Sub<Output = D>, {

    pub fn new(value: T) -> Easer<T> {
        Easer {
            target: value,
            cur: value,
            damping: 0.2,
        }
    }

    pub fn get(&self) -> T {
        self.cur
    }

    pub fn set(&mut self, value: T) {
        self.target = value;
    }

    pub fn step(&mut self) {
        self.cur = self.cur + ((self.target - self.cur) * self.damping);
    }
}

// data structure that tracks whether a value is dirty.
#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize, Hash)]
pub struct LastModified {
    dirty : bool,
    last_modified_ms : SystemTime, // last modified time in milliseconds.
}

impl Default for LastModified {
    fn default() -> Self {
        Self::new()
    }
}

impl LastModified {
    pub fn new() -> LastModified {
        LastModified {
            dirty : true,
            last_modified_ms : SystemTime::now(),
        }
    }

    pub fn modified(&mut self) {
        self.dirty = true;
        self.last_modified_ms = SystemTime::now();
    }

    pub fn union(&mut self, other : &LastModified) {
        // we were modified after the other guy, so we don't need to do
        // consume his event.
        if self.last_modified_ms > other.last_modified_ms {
            return;
        }
        self.last_modified_ms = other.last_modified_ms;
        self.dirty = self.dirty || other.dirty;
    }

    // returns true if the value has been idle for the duration.
    pub fn is_dirty_and_idle_for(&self, duration : std::time::Duration) -> bool {
        if !self.dirty {
            return false;
        }        self.last_modified_ms.elapsed().unwrap_or(std::time::Duration::from_secs(0)) > duration
    }

    pub fn is_dirty(&self) -> bool {
        self.dirty
    }

    pub fn clean(&mut self) {
        self.dirty = false;
        self.last_modified_ms = SystemTime::now();
    }
}

// TODO: refactor API to use pitch class.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, Copy, Hash)]
pub struct PitchClass {
    pub name : PitchName,
    pub accidental : Accidental,
}




impl PitchClass {
    pub fn str(&self) -> String {
        format!("{}{}", self.name.str(), self.accidental.str())
    }

    pub fn enumerate() -> Vec<PitchClass> {
        let mut out = Vec::new();
        // Currently biased towards writing notes as flats, because
        // that's how I prefer to think of the key signatures.
        // Can enharmonically convert to sharps, when needed, based on the key signature.
        out.push(PitchClass { name: PitchName::C, accidental: Accidental::Natural });
        out.push(PitchClass { name: PitchName::D, accidental: Accidental::Flat });
        out.push(PitchClass { name: PitchName::D, accidental: Accidental::Natural });
        out.push(PitchClass { name: PitchName::E, accidental: Accidental::Flat });
        out.push(PitchClass { name: PitchName::E, accidental: Accidental::Natural });
        out.push(PitchClass { name: PitchName::F, accidental: Accidental::Natural });
        out.push(PitchClass { name: PitchName::G, accidental: Accidental::Flat });
        out.push(PitchClass { name: PitchName::G, accidental: Accidental::Natural });
        out.push(PitchClass { name: PitchName::A, accidental: Accidental::Flat });
        out.push(PitchClass { name: PitchName::A, accidental: Accidental::Natural });
        out.push(PitchClass { name: PitchName::B, accidental: Accidental::Flat });
        out.push(PitchClass { name: PitchName::B, accidental: Accidental::Natural });
        out
    }

    pub fn into_pitch(&self, octave : u64) -> Pitch {
        Pitch {
            name: self.name,
            accidental: self.accidental,
            octave,
        }
    }
}

impl fmt::Display for PitchClass {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.str())
    }
}

// a specific pitch, which has a pitch class and an octave.
#[derive(Clone, PartialEq, Serialize, Deserialize, Copy, Hash, Eq)]
pub struct Pitch {
   pub name : PitchName,
   pub accidental : Accidental,
   pub octave : u64,
}

// every pitch class represents a pitch.
impl From<Pitch> for PitchClass {
    fn from(val: Pitch) -> Self {
        PitchClass { name: val.name, accidental: val.accidental }
    }
}

impl Pitch {
  fn new(name : PitchName, accidental : Accidental, octave : u64) -> Self {
    Pitch { name, accidental, octave}
  }

  pub fn pitch (&self) -> i64 {
    (self.octave as i64) * 12 + self.name.pitch() + self.accidental.pitch()
  }

  pub fn into_pitch_class(&self) -> PitchClass {
      PitchClass { name: self.name, accidental: self.accidental }
  }

  pub fn from_pitch (raw_pitch : i64) -> Self {
    assert!(raw_pitch >= 0);
    let octave = raw_pitch / 12 - 1;
    let pitch = raw_pitch % 12;
    let (name, accidental) = match pitch {
        0 => (PitchName::C, Accidental::Natural),
        1 => (PitchName::D, Accidental::Flat),
        2 => (PitchName::D, Accidental::Natural),
        3 => (PitchName::E, Accidental::Flat),
        4 => (PitchName::E, Accidental::Natural),
        5 => (PitchName::F, Accidental::Natural),
        6 => (PitchName::F, Accidental::Sharp),
        7 => (PitchName::G, Accidental::Natural),
        8 => (PitchName::A, Accidental::Flat),
        9 => (PitchName::A, Accidental::Natural),
        10 => (PitchName::B, Accidental::Flat),
        11 => (PitchName::B, Accidental::Natural),
        _ => unreachable!("Impossible case, number is modulo 12: {}", pitch),
    };
    Pitch { name, accidental, octave: octave as u64 }
  }

  pub fn lower_octave(self) -> Pitch {
        Pitch {
            octave: if self.octave > 0 { self.octave - 1 } else { self.octave },
            ..self
        }
    }

    pub fn change_semitones_by(&mut self, delta : i64) -> Pitch {
        Pitch::from_pitch(self.pitch() + delta)
    }

  pub fn raise_octave(self) -> Pitch {
        Pitch {
            octave: self.octave + 1,
            ..self
        }
    }

    pub fn str_no_octave (&self) -> String {
        format!("{}{}", self.name.str(), self.accidental.str())
    }

    pub fn str(&self) -> String {
        format!("{}{}{}", self.name.str(), self.accidental.str(), self.octave)
    }
}

impl fmt::Debug for Pitch {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.str())
    }
}

impl fmt::Display for Pitch {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.str())
    }
}


#[derive(Debug, PartialEq, PartialOrd, Clone, Eq, Hash, Ord, Copy)]
pub enum IntervalKind {
    Unison,
    Minor2nd,
    Major2nd, // diminished
    Minor3rd,
    Major3rd,
    PerfectFourth,
    Tritone,
    PerfectFifth,
    MinorSixth,
    MajorSixth,
    MinorSeventh,
    MajorSeventh,
}

impl IntervalKind {
    pub fn from_pitch_pair(pitch1 : Pitch, pitch2 : Pitch) -> IntervalKind {
        let p = pitch1.pitch() % 12;
        let q = pitch2.pitch() % 12;
        assert!(q + 12 >= p);
        let diff = ((q + 12) - p) % 12;
        assert!((0..12).contains(&diff));
        match diff {
            0 => IntervalKind::Unison,
            1 => IntervalKind::Minor2nd,
            2 => IntervalKind::Major2nd,
            3 => IntervalKind::Minor3rd,
            4 => IntervalKind::Major3rd,
            5 => IntervalKind::PerfectFourth,
            6 => IntervalKind::Tritone,
            7 => IntervalKind::PerfectFifth,
            8 => IntervalKind::MinorSixth,
            9 => IntervalKind::MajorSixth,
            10 => IntervalKind::MinorSeventh,
            11 => IntervalKind::MajorSeventh,
            _ => unreachable!("diff is modulo 12, so can only have values 1..11")
        }
    }
    pub fn pitch(&self) -> i64 {
        match self {
            IntervalKind::Unison => 0,
            IntervalKind::Minor2nd => 1,
            IntervalKind::Major2nd => 2,
            IntervalKind::Minor3rd => 3,
            IntervalKind::Major3rd => 4,
            IntervalKind::PerfectFourth => 5,
            IntervalKind::Tritone => 6,
            IntervalKind::PerfectFifth => 7,
            IntervalKind::MinorSixth => 8,
            IntervalKind::MajorSixth => 9,
            IntervalKind::MinorSeventh => 10,
            IntervalKind::MajorSeventh => 11,
        }
    }

    pub fn str(&self) -> &str {
        match self {
            IntervalKind::Unison => "0",
            IntervalKind::Minor2nd => "m2",
            IntervalKind::Major2nd => "△2",
            IntervalKind::Minor3rd => "m3",
            IntervalKind::Major3rd => "△3",
            IntervalKind::PerfectFourth => "P4",
            IntervalKind::Tritone => "tritone",
            IntervalKind::PerfectFifth => "P5",
            IntervalKind::MinorSixth => "m6",
            IntervalKind::MajorSixth => "△6",
            IntervalKind::MinorSeventh => "m7",
            IntervalKind::MajorSeventh => "M7",
        }
    }

    pub fn diminish(&self) -> IntervalKind {
        match self {
            IntervalKind::Unison => IntervalKind::MajorSeventh,
            IntervalKind::Minor2nd => IntervalKind::Unison,
            IntervalKind::Major2nd => IntervalKind::Minor2nd,
            IntervalKind::Minor3rd => IntervalKind::Major2nd,
            IntervalKind::Major3rd => IntervalKind::Minor3rd,
            IntervalKind::PerfectFourth => IntervalKind::Major3rd,
            IntervalKind::Tritone => IntervalKind::PerfectFourth,
            IntervalKind::PerfectFifth => IntervalKind::Tritone,
            IntervalKind::MinorSixth => IntervalKind::PerfectFifth,
            IntervalKind::MajorSixth => IntervalKind::MinorSixth,
            IntervalKind::MinorSeventh => IntervalKind::MajorSixth,
            IntervalKind::MajorSeventh => IntervalKind::MinorSeventh,
        }
    }
    pub fn augment(&self) -> IntervalKind {
        match self {
            IntervalKind::Unison => IntervalKind::Minor2nd,
            IntervalKind::Minor2nd => IntervalKind::Major2nd,
            IntervalKind::Major2nd => IntervalKind::Minor3rd,
            IntervalKind::Minor3rd => IntervalKind::Major3rd,
            IntervalKind::Major3rd => IntervalKind::PerfectFourth,
            IntervalKind::PerfectFourth => IntervalKind::Tritone,
            IntervalKind::Tritone => IntervalKind::PerfectFifth,
            IntervalKind::PerfectFifth => IntervalKind::MinorSixth,
            IntervalKind::MinorSixth => IntervalKind::MajorSixth,
            IntervalKind::MajorSixth => IntervalKind::MinorSeventh,
            IntervalKind::MinorSeventh => IntervalKind::MajorSeventh,
            IntervalKind::MajorSeventh => IntervalKind::Unison,
        }
    }

    pub fn third() -> IntervalKind {
        IntervalKind::Major3rd
    }

    pub fn diminished_third() -> IntervalKind {
        IntervalKind::Minor3rd
    }

    pub fn augmented_third() -> IntervalKind {
        IntervalKind::PerfectFourth
    }

    pub fn fifth() -> IntervalKind {
        IntervalKind::PerfectFifth
    }

    pub fn diminished_fifth() -> IntervalKind {
        IntervalKind::Tritone
    }

    pub fn augmented_fifth() -> IntervalKind {
        IntervalKind::MinorSixth
    }

    pub fn seventh() -> IntervalKind {
        IntervalKind::MajorSeventh
    }

    pub fn diminished_seventh() -> IntervalKind {
        IntervalKind::MinorSeventh
    }

    // doesn't make much sense to augment a 7th.
    pub fn augmented_seventh() -> IntervalKind {
        IntervalKind::Unison
    }
}

impl Pitch {
    fn increase_pitch(&self, interval: IntervalKind) -> Pitch {
        Pitch::from_pitch(self.pitch() + interval.pitch())
    }

    fn decrease_pitch(&self, interval: IntervalKind) -> Pitch {
        Pitch::from_pitch(self.pitch() - interval.pitch())
    }
}

// implement Pitch + Interval => Pitch
impl std::ops::Add<IntervalKind> for Pitch {
    type Output = Pitch;

    fn add(self, interval: IntervalKind) -> Pitch {
        self.increase_pitch(interval)
    }
}

// impl Pitch - Interval => Pitch
impl std::ops::Sub<IntervalKind> for Pitch {
    type Output = Pitch;

    fn sub(self, interval: IntervalKind) -> Pitch {
        self.decrease_pitch(interval)
    }
}


// Subtract two pitch classes to get an interval
impl std::ops::Sub<PitchClass> for PitchClass {
    type Output = IntervalKind;

    fn sub(self, other: PitchClass) -> IntervalKind {
        // assume that the other pitch is higher than the current pitch.
        IntervalKind::from_pitch_pair(other.into_pitch(0), self.into_pitch(0))
    }
}

// add an interval to a pitch class to get a pitch class.
impl std::ops::Add<IntervalKind> for PitchClass {
    type Output = PitchClass;

    fn add(self, interval: IntervalKind) -> PitchClass {
        let pitch = self.into_pitch(0);
        let new_pitch = pitch + interval;
        new_pitch.into()
    }
}


// an interval is a pair of pitches.
#[derive(Debug, PartialEq, Clone, Hash, Eq, Copy)]
pub struct Interval {
    pitches : (Pitch, Pitch),
}

impl Interval {
    pub fn new (p: Pitch, q: Pitch) -> Interval {
        Interval { pitches: (p, q) }
    }

    pub fn kind(&self) -> IntervalKind {
        IntervalKind::from_pitch_pair(self.pitches.0, self.pitches.1)
    }

    pub fn string(&self) -> String {
        self.kind().str().to_string()
    }
}

impl fmt::Display for Interval {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.string())
    }
}
// impl Pitch - Pitch => Interval
impl std::ops::Sub<Pitch> for Pitch {
    type Output = Interval;

    fn sub(self, other: Pitch) -> Interval {
        Interval::new(self, other)
    }
}

// impl Pitch + Interval => Pitch
impl std::ops::Add<Interval> for Pitch {
    type Output = Pitch;

    fn add(self, interval: Interval) -> Pitch {
        self + interval.kind()
    }
}

// impl Pitch - Interval => Pitch
impl std::ops::Sub<Interval> for Pitch {
    type Output = Pitch;

    fn sub(self, interval: Interval) -> Pitch {
        self - interval.kind()
    }
}

impl fmt::Display for IntervalKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.str())
    }
}



// TODO: extract out the harmonic information into a separate
// data structure: pitchname, accidental, octave.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, Copy)]
pub struct PlayerNote {
    pub x : u64,
    pub start: u64,
    pub nsteps: i64,

    pub pitch : Pitch,
}

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize, Copy)]
enum NoteSelectionPositioning {
    NoteStartsAfterSelection,
    NoteStartsAtSelection,
    NoteProperlyContainsSelection,
    NoteEndsAtSelection,
    NoteEndsBeforeSelection,
    NoteNotInSameTrack,
}

impl NoteSelectionPositioning {
    pub fn plays_sound (&self) -> bool {
        match self {
            NoteSelectionPositioning::NoteStartsAtSelection |
            NoteSelectionPositioning::NoteProperlyContainsSelection => true,
            _ => false,
        }
    }

    pub fn inside_or_ends_at (&self) -> bool {
        match self {
            NoteSelectionPositioning::NoteProperlyContainsSelection |
            NoteSelectionPositioning::NoteEndsAtSelection => true,
            _ => false,
        }
    }
}


fn note_selection_positioning (note : &PlayerNote, selection : Selection) -> NoteSelectionPositioning {
    if selection.x != note.x {
        return NoteSelectionPositioning::NoteNotInSameTrack;
    }
    let end = note.start + note.nsteps as u64;
    if selection.y < note.start {
        return NoteSelectionPositioning::NoteStartsAfterSelection;
    }
    else if selection.y == note.start {
        return NoteSelectionPositioning::NoteStartsAtSelection;
    }
    else if selection.y < end {
        return NoteSelectionPositioning::NoteProperlyContainsSelection;
    }
    else if selection.y == end {
        return NoteSelectionPositioning::NoteEndsAtSelection;
    }
    else if selection.y > end {
        return NoteSelectionPositioning::NoteEndsBeforeSelection;
    }
    panic!("Impossible case");
}


impl PlayerNote {
    pub fn pitch(&self) -> i64 {
        self.pitch.pitch()
    }

    pub fn str (&self) -> String {
        format!("{}{}", self.pitch.name.str(), self.pitch.accidental.str())
    }

    pub fn y(&self) -> u64 {
        self.start
    }

    pub fn lower_octave (&mut self) {
        self.pitch = self.pitch.lower_octave();
    }

    pub fn raise_octave(&mut self) {
        self.pitch = self.pitch.raise_octave();
    }

    pub fn insert_newline_at (&self, selection : Selection, accum : &mut Vec<PlayerNote>) {
        let pos = note_selection_positioning(self, selection);
        match pos {
            NoteSelectionPositioning::NoteStartsAtSelection |
            NoteSelectionPositioning::NoteNotInSameTrack |
            NoteSelectionPositioning::NoteEndsAtSelection |
            NoteSelectionPositioning::NoteEndsBeforeSelection => {
                // note ends before selection, so it is unaffected.
                accum.push(*self);
            },
            NoteSelectionPositioning::NoteStartsAfterSelection => {
                // note starts after selection, so move note down.
                let mut out = *self;
                out.start += 1;
                accum.push(out);
            },
            NoteSelectionPositioning::NoteProperlyContainsSelection => {
                let end = self.start + self.nsteps as u64;
                let mut n2 = *self;
                n2.start = selection.y;
                n2.nsteps = (end - n2.start) as i64;
                assert!(n2.nsteps > 0); // must be the case, as interval properly contains selection.

                let mut n1 = *self;
                n1.nsteps = (selection.y - n1.start) as i64;

                if n1.nsteps > 0 {
                    accum.push(n1);
                }
            }
        }
    }

    // returns true if something of significance was consumed.
    // return the new selection.
    // return true if the stuff was consumed.
    pub fn delete_line (&self, selection : Selection, accum : &mut Vec<PlayerNote>) -> bool {
        match note_selection_positioning(self, selection) {
            NoteSelectionPositioning::NoteEndsAtSelection |
            NoteSelectionPositioning::NoteStartsAfterSelection => {
                // note starts after selection, so move note up.
                let mut out = *self;
                out.start = if out.start > 0 { out.start - 1 } else { 0 };
                accum.push(out);
                false
            },
            NoteSelectionPositioning::NoteStartsAtSelection |
            NoteSelectionPositioning::NoteProperlyContainsSelection => {
                // note properly contains selection, or ends at the cursor,
                // so we consume it.
                let mut out = *self;
                out.nsteps = self.nsteps - 1;
                if out.nsteps > 0 {
                    accum.push(out);
                }
                true
            },
            NoteSelectionPositioning::NoteNotInSameTrack |
            NoteSelectionPositioning::NoteEndsBeforeSelection => {
                // note ends before selection, so it is unaffected.
                accum.push(*self);
                false
            },
        }
    }

    pub fn decrease_nsteps (&self) -> Option<PlayerNote> {
        let mut note = *self;
        if note.nsteps > 1 {
            note.nsteps -= 1;
            Some(note)
        } else {
            None
        }
    }

    pub fn increase_nsteps (&self) -> PlayerNote {
        let mut note = *self;
        // TODO: what should happen to a note with duration zero?
        note.nsteps += 1;
        note
    }
}

#[derive (Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Hitbox {
    starts_or_contains : HashMap<(u64, u64), usize>,
    contains_or_ends_at : HashMap<(u64, u64), usize>,
}

impl Hitbox {
    pub fn new() -> Hitbox {
        Hitbox {
            starts_or_contains : HashMap::new(),
            contains_or_ends_at : HashMap::new(),
        }
    }

    fn starts_or_contains (&self, selection : &Selection) -> Option<usize> {
        self.starts_or_contains.get(&(selection.x, selection.y)).copied()
    }

    fn contains_or_ends_at (&self, selection : &Selection) -> Option<usize> {
        self.contains_or_ends_at.get(&(selection.x, selection.y)).copied()
    }

    fn build (notes : &Vec<PlayerNote>) -> Hitbox {
        let mut starts_or_contains = HashMap::new();
        let mut contains_or_ends_at = HashMap::new();
        for (ix, note) in notes.iter().enumerate() {
            assert!(note.nsteps > 0);
            for y in note.start..note.start + (note.nsteps as u64) + 1{
                assert!(note.start != 0);
                // can't have another note at the same location.
                if y != (note.start + note.nsteps as u64) {
                    assert!(!starts_or_contains.contains_key(&(note.x, y)));
                    starts_or_contains.insert((note.x, y), ix);
                }
                if y != note.start {
                    assert!(!contains_or_ends_at.contains_key(&(note.x, y)));
                    contains_or_ends_at.insert((note.x, y), ix);
                }
            }
        }
        Hitbox {  starts_or_contains, contains_or_ends_at }
    }

}

// information that is saved when a track is saved.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
pub struct PlayerTrackSaveInfo {
    pub notes : Vec<PlayerNote>
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
#[serde(from = "PlayerTrackSaveInfo", into = "PlayerTrackSaveInfo")]
pub struct PlayerTrack {
    // TODO: make this immutable vector with imrs
    pub notes: Vec<PlayerNote>, // sorted by start
    // TODO: make this immutable vector with imrs
    // TODO: rebuild this, instead of storing it via serde.
    hitbox : Hitbox,
    pub last_modified : LastModified
}

impl Default for PlayerTrack {
    fn default() -> Self {
        Self::new()
    }
}

impl From<PlayerTrack> for PlayerTrackSaveInfo {
    fn from(val: PlayerTrack) -> Self {
        PlayerTrackSaveInfo {
            notes: val.notes
        }
    }
}

impl From<PlayerTrackSaveInfo> for PlayerTrack {
    fn from(info: PlayerTrackSaveInfo) -> Self {
        PlayerTrack::from_notes(info.notes)
    }
}

impl PlayerTrack {
    pub fn new() -> PlayerTrack {
        PlayerTrack {
            notes: Vec::new(),
            last_modified: LastModified::new(),
            hitbox : Hitbox::new(),
        }
    }

    pub fn from_notes(notes : Vec<PlayerNote>) -> PlayerTrack {
        PlayerTrack {
            hitbox : Hitbox::build(&notes),
            last_modified: LastModified::new(),
            notes,
        }
    }


    pub fn add_note (&mut self, note : PlayerNote) {
        self.notes.push(note);
        self.hitbox = Hitbox::build(&self.notes);
        self.last_modified.modified();
    }


    pub fn get_note_from_coord (&self, x : u64, y : u64) -> Option<PlayerNote> {
        self.hitbox.starts_or_contains(&Selection { x, y }).map(|ix| self.notes[ix])
    }

    pub fn get_note_ix_from_coord (&self, x : u64, y : u64) -> Option<usize> {
        self.hitbox.starts_or_contains(&Selection {x, y})
    }

    pub fn modify_note_at_ix_mut (&mut self, ix : usize, f : impl FnOnce(&mut PlayerNote)) {
        self.last_modified.modified();
        assert!(ix < self.notes.len());
        f(&mut self.notes[ix]);
        self.hitbox = Hitbox::build(&self.notes);
    }

    pub fn get_last_instant (&self) -> u64 {
        self.notes.iter().map(|note| note.start + note.nsteps as u64).max().unwrap_or(0)
    }

    fn insert_newline (&mut self, selection : Selection) {
        self.last_modified.modified();
        let mut new_notes = Vec::new();
        for note in self.notes.iter() {
            note.insert_newline_at(selection, &mut new_notes);
        }
        self.notes = new_notes;
        self.hitbox = Hitbox::build(&self.notes);
    }

    // return true if something was consumed.
    fn delete_line (&mut self, selection : Selection) -> bool {
        self.last_modified.modified();
        match self.hitbox.starts_or_contains(&selection) {
            Some(ix) => {
                let mut note = self.notes[ix];

                assert!(note.nsteps >= 1);
                note.nsteps -= 1;
                if note.nsteps == 0 {
                    self.notes.remove(ix);
                } else {
                    self.notes[ix] = note;
                }
                self.hitbox = Hitbox::build(&self.notes);
                true
            }

            None => {
                // no note lies at this location, so we need to move notes up.
                for note in self.notes.iter_mut() {
                    let relation = note_selection_positioning(note, selection);
                    // if the note starts after the selection, we need to move it up.
                    if relation == NoteSelectionPositioning::NoteStartsAfterSelection {
                        // notes start at 1.
                        // zero is hallowed ground where no note may rest.
                        if note.start >= 2 {
                            note.start -= 1;
                        }
                    }
                }
                self.hitbox = Hitbox::build(&self.notes);
                false
            }
        }
    }

    fn increase_nsteps (&mut self, selection : Selection) {
        self.last_modified.modified();
        if let Some(ix) = self.hitbox.starts_or_contains(&selection) {
            let note = self.notes[ix];

            // do we need to make space for more notes? yes we do!
            for bumped_note in self.notes.iter_mut() {
                // the other note starts at or after the note we just bumped,
                // so we need to push it down to make space for it!
                if bumped_note.x == selection.x &&  bumped_note.start >= note.start + note.nsteps as u64 {
                    bumped_note.start += 1;
                }
            }


            // now that we've made space, adjust the current note.
            self.notes[ix] = note.increase_nsteps();
            self.hitbox = Hitbox::build(&self.notes);
        }
    }

    fn decrease_nsteps (&mut self, selection : Selection) {
        self.last_modified.modified();
        if let Some(ix) = self.hitbox.starts_or_contains(&selection) {
            let note = self.notes[ix];

            // we need to delete space that was occupied by this note.
            for bumped_note in self.notes.iter_mut() {
                // the other note starts at or after the note we just bumped,
                // so we need to push it down to make space for it!
                if bumped_note.x == selection.x &&
                    bumped_note.start >= note.start + note.nsteps as u64 {
                    assert!(bumped_note.start >= 2);
                    bumped_note.start -= 1;
                }
            }

            if let Some(new_note) = note.decrease_nsteps() {
                self.notes[ix] = new_note; // we've decreased the duration of this note.
            } else {
                // we've deleted this note.
                // TODO: keep this around, until someone tells us that the increase/decrease manipulation
                // has ended, at which point we can delete the tombstone values.
                self.notes.remove(ix);
            }
            self.hitbox = Hitbox::build(&self.notes);
        }
    }


}

// MIDI_sample from wikimedia.
// https://en.wikipedia.org/wiki/File:MIDI_sample.mid?qsrc=3044
// >>> mid = mido.MidiFile("MIDI_sample.mid")
// >>> mid
// MidiFile(type=1, ticks_per_beat=480, tracks=[
//   MidiTrack([
//     MetaMessage('track_name', name='Wikipedia MIDI (extended)', time=0),
//     MetaMessage('set_tempo', tempo=500000, time=0),
//     MetaMessage('time_signature', numerator=4, denominator=4, clocks_per_click=24, notated_32nd_notes_per_beat=8, time=0),
//     MetaMessage('end_of_track', time=0)]),
//   MidiTrack([
//     MetaMessage('track_name', name='Bass', time=0),
//     Message('control_change', channel=0, control=0, value=121, time=0),
//     Message('control_change', channel=0, control=32, value=0, time=0),
//     Message('program_change', channel=0, program=33, time=0),
//     Message('note_on', channel=0, note=45, velocity=78, time=0),
//     Message('note_off', channel=0, note=45, velocity=64, time=256),
//     ...
// Message('note_on', channel=2, note=64, velocity=0, time=26),
// Message('note_on', channel=2, note=57, velocity=0, time=515),
// MetaMessage('end_of_track', time=0)])//


#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize, Eq, Hash)]
pub enum PitchName {
    C,
    D,
    E,
    F,
    G,
    A,
    B,
}


impl PitchName {
    pub fn str(&self) -> &str {
        match self {
            PitchName::C => "C",
            PitchName::D => "D",
            PitchName::E => "E",
            PitchName::F => "F",
            PitchName::G => "G",
            PitchName::A => "A",
            PitchName::B => "B",
        }
    }

  pub fn pitch (&self) -> i64 {
      match self {
          PitchName::C => 0,
          PitchName::D => 2,
          PitchName::E => 4,
          PitchName::F => 5,
          PitchName::G => 7,
          PitchName::A => 9,
          PitchName::B => 11,
      }
  }
}

impl fmt::Display for PitchName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.str())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize, Eq, Hash)]
pub enum Accidental {
    Natural,
    Sharp,
    Flat,
}

impl Accidental {
    pub fn str(&self) -> &str {
        match self {
            Accidental::Natural => "",
            Accidental::Sharp => "#",
            Accidental::Flat => "b",
        }
    }

    pub fn of_lean(ix : u64) -> Accidental {
        match ix {
            0 => Accidental::Natural,
            1 => Accidental::Sharp,
            2 => Accidental::Flat,
            _ => panic!("Invalid accidental index {}", ix),
        }
    }

    pub fn toggle_sharp (&self) -> Accidental{
        match self {
            Accidental::Natural => Accidental::Sharp,
            Accidental::Sharp => Accidental::Natural,
            Accidental::Flat => Accidental::Natural,
        }
    }

    pub fn toggle_flat (&self) -> Accidental {
        match self {
            Accidental::Natural => Accidental::Flat,
            Accidental::Sharp => Accidental::Natural,
            Accidental::Flat => Accidental::Natural,
        }
    }

    pub fn pitch (&self) -> i64 {
        match self {
            Accidental::Natural => 0,
            Accidental::Sharp => 1,
            Accidental::Flat => -1,
        }
    }

}

impl fmt::Display for Accidental {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.str())
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, Copy)]
pub struct Selection {
    pub x : u64,
    pub y : u64,
}

impl Selection {
    fn new() -> Selection {
        Selection {
            x: 0,
            y: 1,
        }
    }

    // we don't allow insertion at location 0, but we do allow
    // a creation of a cursor that sits at zero for e.g. newline creation.
    fn legalize_for_insert(&self) -> Selection {
        Selection {
            x: self.x,
            y: if self.y <= 1 { 1 } else { self.y }
        }
    }

    fn move_left_one(&self) -> Selection {
        Selection {
            x : if self.x == 0 { 0 } else { self.x - 1 },
            y : self.y
        }
    }

    fn move_right_one(&self) -> Selection {
        Selection {
            x : if self.x == NTRACKS - 1 { NTRACKS - 1 } else { self.x + 1 },
            y : self.y
        }
    }

    fn move_down_one(&self) -> Selection {
        Selection {
            x : self.x,
            y : if self.y == TRACK_LENGTH - 1 { TRACK_LENGTH - 1 } else { self.y + 1 }
        }
    }

    fn move_up_one(&self) -> Selection {
        Selection {
            x : self.x,
            y : if self.y == 0 { 0 } else { self.y - 1 }
        }
    }

    pub fn cursor(&self) -> egui::Pos2 {
        egui::Pos2::new(self.x as f32, self.y as f32)
    }

}

#[derive(Debug, PartialEq, Serialize, Deserialize, Clone)]
pub enum Action {
    CursorMoveLeftOne,
    CursorMoveRightOne,
    CursorMoveDownOne,
    CursorMoveUpOne,
    ToggleSharp,
    ToggleFlat,
    Newline,
    DeleteLine,
    LowerOctave,
    RaiseOctave,
    IncreaseNSteps,
    DecreaseNSteps,
}

#[derive (Debug, PartialEq, Serialize, Deserialize, Clone)]
#[serde(from = "HistorySaveInfo", into = "HistorySaveInfo")]
pub struct History {
    actions : Vec<(Action, Selection, PlayerTrack)>,
    current : usize,
}

#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct HistorySaveInfo {
    pub actions : Vec<(Action, Selection, PlayerTrackSaveInfo)>,
    pub current : usize,
}

impl From<HistorySaveInfo> for History {
    fn from(info: HistorySaveInfo) -> Self {
        History {
            actions: info.actions.into_iter().map(|(action, selection, track)| {
                (action, selection, PlayerTrack::from_notes(track.notes))
            }).collect(),
            current: info.current,
        }
    }
}

impl From<History> for HistorySaveInfo {
    fn from(val: History) -> Self {
        HistorySaveInfo {
            actions: val.actions.into_iter().map(|(action, selection, track)| {
                (action, selection, track.into())
            }).collect(),
            current: val.current,
        }
    }
}

impl History {
    fn new() -> History {
        History {
            actions: Vec::new(),
            current: 0,
        }
    }

    fn push(&mut self, action : Action, selection : Selection, track : PlayerTrack) {
        self.actions.truncate(self.current);
        self.actions.push((action, selection, track));
        self.current += 1;

        if self.actions.len() > NUM_HISTORY_STEPS {
            self.actions.drain(0..(self.actions.len() - NUM_HISTORY_STEPS));
        }
    }

    fn undo(&mut self) -> Option<(Action, Selection, PlayerTrack)> {
        if self.current == 0 {
            None
        } else {
            self.current -= 1;
            Some(self.actions[self.current].clone())
        }
    }

    fn redo(&mut self) -> Option<(Action, Selection, PlayerTrack)> {
        if self.current == self.actions.len() {
            None
        } else {
            self.current += 1;
            Some(self.actions[self.current - 1].clone())
        }
    }
}


#[derive(Debug, PartialEq, Serialize, Deserialize, Clone, Copy)]
enum MusicMode {
    Major, // Ionian
    HarmonicMinor, // Minor
    // Aeolian / NaturalMinor
}

#[derive(Debug, PartialEq, Serialize, Deserialize, Clone, Copy)]
pub struct KeySignature {
    pub key : PitchClass,
    // TODO: add mode into the key signature.
    // pub allowed_pitch_classes : Vec<PitchClass>,
}

impl MusicMode {

    // return a sequence of intervals, as measured from the root,
    // that generate the scale.
    pub fn get_intervals_from_root(&self) -> Vec<IntervalKind> {
        match self {
            MusicMode::Major => vec![
                IntervalKind::Unison,
                IntervalKind::Major2nd,
                IntervalKind::Major3rd,
                IntervalKind::PerfectFourth,
                IntervalKind::PerfectFifth,
                IntervalKind::MajorSixth,
                IntervalKind::MajorSeventh,
            ],
            MusicMode::HarmonicMinor => vec![
                IntervalKind::Unison,
                IntervalKind::Major2nd,
                IntervalKind::Minor3rd,
                IntervalKind::PerfectFourth,
                IntervalKind::PerfectFifth,
                IntervalKind::MinorSixth,
                IntervalKind::MajorSeventh,
            ],

        }

    }

    // get the scale (a sequence of pitch classes) for a given key signature.
    pub fn get_scale(&self, k : KeySignature) -> Vec<PitchClass> {
        let mut scale = Vec::new();
        let intervals = self.get_intervals_from_root();
        let root = k.key;
        for interval in intervals.iter() {
            scale.push(root + *interval);
        }
        scale
    }
}

impl Default for KeySignature {
    // C minor mode.
    fn default() -> KeySignature {
        KeySignature {
            key : PitchClass {
                name : PitchName::C,
                accidental : Accidental::Natural,
            },
        }
    }
}

// information that is saved when a project is saved.
#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct ProjectSaveInfo {
    pub track_name : String,
    pub artist_name : String,
    pub time_signature : (u8, u8),
    pub track : PlayerTrackSaveInfo,
    pub history : HistorySaveInfo,
    pub key_signature : KeySignature,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(from = "ProjectSaveInfo", into = "ProjectSaveInfo")]
pub struct Project {
    pub last_modified : LastModified,
    pub track : PlayerTrack,
    pub selection : Selection,
    pub playback_speed : f64,
    pub track_name : String,
    pub artist_name : String,
    pub time_signature : (u8, u8),
    pub history : History,
    pub counterpoint1 : CounterpointLints,
    pub chord_info : ChordInfo,
    pub key_signature : KeySignature,
}

impl From<ProjectSaveInfo> for Project {
    fn from(info: ProjectSaveInfo) -> Self {
        let track = PlayerTrack::from_notes(info.track.notes);
        let cp = CounterpointLints::from_track(&track);
        let mut chord_info  : ChordInfo = Default::default();
        chord_info.rebuild(&track, info.key_signature);
        Project {
            last_modified: LastModified::new(),
            track,
            selection: Selection::new(),
            playback_speed: 0.2,
            track_name: info.track_name,
            artist_name: info.artist_name,
            time_signature: info.time_signature,
            history: info.history.into(),
            counterpoint1 : cp,
            chord_info,
            key_signature : info.key_signature,
        }
    }
}

impl From<Project> for ProjectSaveInfo {
    fn from(val: Project) -> Self {
        ProjectSaveInfo {
            track_name: val.track_name,
            artist_name: val.artist_name,
            time_signature: val.time_signature,
            track: val.track.into(),
            history: val.history.into(),
            key_signature : val.key_signature,
        }
    }
}

impl Project {

    // TODO: take egui context to set title.
    pub fn new(track_name : String) -> Project {
        Project {
            last_modified : LastModified::new(),
            track: PlayerTrack::new(),
            selection: Selection::new(),
            playback_speed: 1.0,
            track_name,
            artist_name: "Unknown".to_string(),
            time_signature: (4, 4),
            history: History::new(),
            counterpoint1 : Default::default(),
            chord_info : Default::default(),
            key_signature : Default::default(),
        }
    }

    pub fn set_pitch (&mut self, pitch : PitchName) {
        self.last_modified.modified();
        self.selection = self.selection.legalize_for_insert();
        if let Some(ix) = self.track.get_note_ix_from_coord(self.selection.x, self.selection.y) {
            self.history.push(Action::ToggleSharp, self.selection, self.track.clone());
            self.track.modify_note_at_ix_mut(ix, |note| {
                note.pitch.name = pitch
            });
        } else {
            // otherwise, add a note.
            self.track.add_note(PlayerNote {
                x: self.selection.x,
                start: self.selection.y,
                nsteps: 1,
                pitch : Pitch {
                name: pitch,
                accidental: Accidental::Natural,
                octave: 4,
                }
            });
            // self.cursor_move_down_one(); this makes it annoying when one wants to e.g. write C#
        }
        self.chord_info.rebuild(&self.track, self.key_signature);
    }

    pub fn cursor_move_left_one (&mut self) {
        self.last_modified.modified();
        self.history.push(Action::CursorMoveLeftOne, self.selection, self.track.clone());
        self.selection = self.selection.move_left_one();
        self.chord_info.rebuild(&self.track, self.key_signature);
    }

    pub fn cursor_move_right_one (&mut self) {
        self.history.push(Action::CursorMoveRightOne, self.selection, self.track.clone());
        self.selection = self.selection.move_right_one();
        self.chord_info.rebuild(&self.track, self.key_signature);
    }

    pub fn cursor_move_down_one (&mut self) {
        self.last_modified.modified();
        self.history.push(Action::CursorMoveDownOne, self.selection, self.track.clone());
        self.selection = self.selection.move_down_one();
        self.chord_info.rebuild(&self.track, self.key_signature);
    }

    pub fn cursor_move_up_one (&mut self) {
        self.last_modified.modified();
        self.history.push(Action::CursorMoveUpOne, self.selection, self.track.clone());
        self.selection = self.selection.move_up_one();
        self.chord_info.rebuild(&self.track, self.key_signature);
    }

    pub fn toggle_sharp (&mut self) {
        if let Some(ix) = self.track.get_note_ix_from_coord(self.selection.x, self.selection.y) {
            self.last_modified.modified();
            self.history.push(Action::ToggleSharp, self.selection, self.track.clone());
            self.track.modify_note_at_ix_mut(ix, |note| {
                note.pitch.accidental = note.pitch.accidental.toggle_sharp()
            });
            self.chord_info.rebuild(&self.track, self.key_signature);
        }
    }

    pub fn toggle_flat (&mut self) {
        if let Some(ix) = self.track.get_note_ix_from_coord(self.selection.x, self.selection.y) {
            self.last_modified.modified();
            self.history.push(Action::ToggleFlat, self.selection, self.track.clone());
            self.track.modify_note_at_ix_mut(ix, |note| {
                note.pitch.accidental = note.pitch.accidental.toggle_flat()
            });
            self.chord_info.rebuild(&self.track, self.key_signature);
        }
    }

    pub fn newline (&mut self) {
        self.last_modified.modified();
        self.history.push(Action::Newline, self.selection, self.track.clone());
        self.track.insert_newline(self.selection);
        self.selection = self.selection.move_down_one();
        self.chord_info.rebuild(&self.track, self.key_signature);
    }

    pub fn delete_line (&mut self) {
        if self.selection.y == 0 { return; }
        self.last_modified.modified();
        self.history.push(Action::DeleteLine, self.selection, self.track.clone());
        // this lets cursor eat things like:
        // A A A| -> A A|A -> A A |- , since the cursor eats things *below*.
        let consumed = self.track.delete_line(self.selection);
        if !consumed {
            // if nothing was consumed, then we make an action by moving the cursor up.
            self.selection = self.selection.move_up_one();
        }
        self.chord_info.rebuild(&self.track, self.key_signature);
    }

    pub fn lower_octave (&mut self) {
        if let Some(ix) = self.track.get_note_ix_from_coord(self.selection.x, self.selection.y) {
            self.last_modified.modified();
            self.history.push(Action::LowerOctave, self.selection, self.track.clone());
            self.track.modify_note_at_ix_mut(ix, |note| {
                note.lower_octave()
            });
            self.chord_info.rebuild(&self.track, self.key_signature);
        }
    }

    pub fn raise_octave (&mut self) {
        if let Some(ix) = self.track.get_note_ix_from_coord(self.selection.x, self.selection.y) {
            self.last_modified.modified();
            self.history.push(Action::RaiseOctave, self.selection, self.track.clone());
            self.track.modify_note_at_ix_mut(ix, |note| {
                note.raise_octave()
            });
            self.chord_info.rebuild(&self.track, self.key_signature);
        }
    }

    pub fn increase_nsteps (&mut self) {
        self.last_modified.modified();
        self.history.push(Action::IncreaseNSteps, self.selection, self.track.clone());
        self.track.increase_nsteps(self.selection);
        // TODO: call this on each frame, and cache if key signature has been modified.
        self.chord_info.rebuild(&self.track, self.key_signature);
    }

    pub fn decrease_nsteps (&mut self) {
        self.last_modified.modified();
        self.history.push(Action::DecreaseNSteps, self.selection, self.track.clone());
        self.track.decrease_nsteps(self.selection);
        self.chord_info.rebuild(&self.track, self.key_signature);
    }

    pub fn undo_action (&mut self) {
        match self.history.undo() {
            Some((_action, selection, track)) => {
                self.chord_info.rebuild(&track, self.key_signature);
                self.last_modified.modified();
                self.selection = selection;
                self.track = track;
                self.track.last_modified.modified();
            },
            None => {
                event!(Level::INFO, "No more actions to undo");
            }
        }
    }

    pub fn redo_action (&mut self) {
        match self.history.redo() {
            Some((_action, selection, track)) => {
                self.chord_info.rebuild(&track, self.key_signature);
                self.last_modified.modified();
                self.selection = selection;
                self.track = track;
                self.track.last_modified.modified();
            },
            None => {
                event!(Level::INFO, "No more actions to redo");
            }
        }
    }
    pub fn get_app_title(&self) -> String {
        format!("monodrone({})", self.track_name)
    }

    pub fn to_smf(&self) -> (midly::Header, Vec<midly::Track>) {
        let header = midly::Header {
            format: midly::Format::Parallel,
            timing: midly::Timing::Metrical(midly::num::u15::from_int_lossy(480)),
        };

        let mut meta_track = midly::Track::new();
        meta_track.push(midly::TrackEvent {
            delta: 0.into(),
            kind: midly::TrackEventKind::Meta(midly::MetaMessage::TrackName(self.track_name.as_bytes())),
        });
        meta_track.push(midly::TrackEvent {
            delta: 0.into(),
            kind: midly::TrackEventKind::Meta(midly::MetaMessage::Tempo(midly::num::u24::from_int_lossy(500000))),
        });
        meta_track.push(midly::TrackEvent {
            delta: 0.into(),
            kind: midly::TrackEventKind::Meta(midly::MetaMessage::TimeSignature(
                self.time_signature.0, // numerator: 4,
                self.time_signature.1, // denominator: 4,
                24, // metronome: 24,
                8, // thirty_seconds: 8,
            )),
        });
        meta_track.push(midly::TrackEvent {
            delta: 0.into(),
            kind: midly::TrackEventKind::Meta(midly::MetaMessage::EndOfTrack),
        });

        // TODO: consider adding a track that has metadata.
        let mut track = midly::Track::new();

        track.push(midly::TrackEvent {
            delta: 0.into(),
            kind: midly::TrackEventKind::Meta(midly::MetaMessage::TrackName(self.track_name.as_bytes())),
        });
        track.push(midly::TrackEvent {
            delta: 0.into(),
            kind: midly::TrackEventKind::Midi {
                channel: 0.into(),
                message: midly::MidiMessage::Controller {
                    controller: 0.into(), // select patch.
                    value: 121.into(),
                },
            },
        });
        track.push(midly::TrackEvent {
            delta: 0.into(),
            kind: midly::TrackEventKind::Midi {
                channel: 0.into(),
                message: midly::MidiMessage::Controller {
                    controller: 32.into(), // controller LSB?
                    value: 0.into(),
                },
            },
        });
        track.push(midly::TrackEvent {
            delta: 0.into(),
            kind: midly::TrackEventKind::Midi {
                channel: 0.into(),
                message: midly::MidiMessage::ProgramChange {
                    program: 0.into(), // grand piano
                },
            },
        });

        let mut max_time = 0;
        for note in self.track.notes.iter() {
            let end = note.start + note.nsteps as u64;
            assert!(end > note.start);
            max_time = max_time.max(end);
        }
        let time_delta : u32 = (256.0 / self.playback_speed) as u32;
        let mut time_delta_accum = 0;
        for t in 0..max_time+1 {
            time_delta_accum += time_delta; // for this instant of time, add time.
            let player_notes = track_get_note_events_at_time(&self.track, t);
            for (_i, player_note) in player_notes.iter().enumerate() {
                let time_delta = time_delta_accum;
                time_delta_accum = 0; // we've consumed the time delta for this note.
                let midi_message = player_note.to_midi_message();
                let midi_note = midly::TrackEventKind::Midi {
                    channel : 0.into(),
                    message : midi_message
                };
                track.push(midly::TrackEvent {
                    delta: time_delta.into(),
                    kind: midi_note
                });
            }
        };

        track.push(midly::TrackEvent {
            delta: 0.into(),
            kind: midly::TrackEventKind::Meta(midly::MetaMessage::EndOfTrack),
        });
        (header, vec![meta_track, track])
    }

}

impl Clone for Project {
    fn clone(&self) -> Self {
        Project {
            last_modified : self.last_modified,
            track: self.track.clone(),
            selection: self.selection,
            playback_speed: self.playback_speed,
            track_name: self.track_name.clone(),
            artist_name: self.artist_name.clone(),
            time_signature: self.time_signature,
            history: self.history.clone(),
            counterpoint1 : self.counterpoint1.clone(),
            chord_info : self.chord_info.clone(),
            key_signature : self.key_signature,
        }
    }
}
