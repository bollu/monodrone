use serde::{Serialize, Deserialize};
use std::time::SystemTime;
use std::collections::HashMap;
use tracing::{event, Level};

use crate::counterpoint1::CounterpointLints;
use crate::midi::track_get_note_events_at_time;

#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize, Hash)]


// data structure that tracks whether a value is dirty.
pub struct LastModified {
    pub dirty : bool,
    pub last_modified_ms : SystemTime, // last modified time in milliseconds.
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

    pub fn clean(&mut self) {
        self.dirty = false;
        self.last_modified_ms = SystemTime::now();
    }
}

trait Dirt {
    fn get_dirty(&self) -> &LastModified;
    fn get_dirty_mut(&self) -> &mut LastModified;
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, Copy)]
pub struct Pitch {
   pub name : PitchName,
   pub accidental : Accidental,
   pub octave : u64,
}

impl Pitch {
  fn new(name : PitchName, accidental : Accidental, octave : u64) -> Self {
    Pitch { name, accidental, octave}
  }

  pub fn pitch (&self) -> i64 {
    (self.octave as i64 + 1) * 12 + self.name.pitch() + self.accidental.pitch()
  }

  pub fn lower_octave(&mut self) {
        if self.octave > 0 {
            self.octave -= 1;
        }
    }

  pub fn raise_octave(&mut self) {
        self.octave += 1;
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
        self.pitch.lower_octave();
    }

    pub fn raise_octave(&mut self) {
        self.pitch.raise_octave();
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
    last_modified : LastModified
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


#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
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

#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
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

pub const NTRACKS : u64 = 4;
pub const TRACK_LENGTH : u64 = 100;


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

// information that is saved when a project is saved.
#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct ProjectSaveInfo {
    pub track_name : String,
    pub artist_name : String,
    pub time_signature : (u8, u8),
    pub track : PlayerTrackSaveInfo,
    pub history : HistorySaveInfo,
}

#[derive(Debug, PartialEq, Serialize, Deserialize)]
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
}

impl From<ProjectSaveInfo> for Project {
    fn from(info: ProjectSaveInfo) -> Self {
        let track = PlayerTrack::from_notes(info.track.notes);
        let cp = CounterpointLints::from_track(&track);
        Project {
            last_modified: LastModified::new(),
            track,
            selection: Selection::new(),
            playback_speed: 1.0,
            track_name: info.track_name,
            artist_name: info.artist_name,
            time_signature: info.time_signature,
            history: info.history.into(),
            counterpoint1 : cp,
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
    }

    pub fn cursor_move_left_one (&mut self) {
        self.last_modified.modified();
        self.history.push(Action::CursorMoveLeftOne, self.selection, self.track.clone());
        self.selection = self.selection.move_left_one();
    }

    pub fn cursor_move_right_one (&mut self) {
        self.history.push(Action::CursorMoveRightOne, self.selection, self.track.clone());
        self.selection = self.selection.move_right_one();
    }

    pub fn cursor_move_down_one (&mut self) {
        self.last_modified.modified();
        self.history.push(Action::CursorMoveDownOne, self.selection, self.track.clone());
        self.selection = self.selection.move_down_one();
    }

    pub fn cursor_move_up_one (&mut self) {
        self.last_modified.modified();
        self.history.push(Action::CursorMoveUpOne, self.selection, self.track.clone());
        self.selection = self.selection.move_up_one();
    }

    pub fn toggle_sharp (&mut self) {
        if let Some(ix) = self.track.get_note_ix_from_coord(self.selection.x, self.selection.y) {
            self.last_modified.modified();
            self.history.push(Action::ToggleSharp, self.selection, self.track.clone());
            self.track.modify_note_at_ix_mut(ix, |note| {
                note.pitch.accidental = note.pitch.accidental.toggle_sharp()
            });
        }
    }

    pub fn toggle_flat (&mut self) {
        if let Some(ix) = self.track.get_note_ix_from_coord(self.selection.x, self.selection.y) {
            self.last_modified.modified();
            self.history.push(Action::ToggleFlat, self.selection, self.track.clone());
            self.track.modify_note_at_ix_mut(ix, |note| {
                note.pitch.accidental = note.pitch.accidental.toggle_flat()
            });
        }
    }

    pub fn newline (&mut self) {
        self.last_modified.modified();
        self.history.push(Action::Newline, self.selection, self.track.clone());
        self.track.insert_newline(self.selection);
        self.selection = self.selection.move_down_one();
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
    }

    pub fn lower_octave (&mut self) {
        if let Some(ix) = self.track.get_note_ix_from_coord(self.selection.x, self.selection.y) {
            self.last_modified.modified();
            self.history.push(Action::LowerOctave, self.selection, self.track.clone());
            self.track.modify_note_at_ix_mut(ix, |note| {
                note.lower_octave()
            });
        }
    }

    pub fn raise_octave (&mut self) {
        if let Some(ix) = self.track.get_note_ix_from_coord(self.selection.x, self.selection.y) {
            self.last_modified.modified();
            self.history.push(Action::RaiseOctave, self.selection, self.track.clone());
            self.track.modify_note_at_ix_mut(ix, |note| {
                note.raise_octave()
            });
        }
    }

    pub fn increase_nsteps (&mut self) {
        self.last_modified.modified();
        self.history.push(Action::IncreaseNSteps, self.selection, self.track.clone());
        self.track.increase_nsteps(self.selection);
    }

    pub fn decrease_nsteps (&mut self) {
        self.last_modified.modified();
        self.history.push(Action::DecreaseNSteps, self.selection, self.track.clone());
        self.track.decrease_nsteps(self.selection);
    }

    pub fn undo_action (&mut self) {
        match self.history.undo() {
            Some((_action, selection, track)) => {
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
        }
    }
}
