
use std::{collections::HashMap, path::PathBuf, sync::Arc};
use egui::PlatformOutput;
use lean_sys::{lean_box, lean_dec_ref, lean_inc_ref, lean_io_result_get_error, lean_object, lean_unbox_float};
use serde::{Serialize, Deserialize};


use tracing::{event, Level};

use crate::{track_get_note_events_at_time};

#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub struct PlayerNote {
    pub x : u64,
    pub start: u64,
    pub nsteps: i64,

    pub pitch_name: PitchName,
    pub accidental : Accidental,
    pub octave : u64,
}

fn octave_to_midi_pitch (octave : u64) -> u64 {
    12 * (octave + 1)
}

fn pitch_name_to_midi_pitch (pitch_name : PitchName) -> u64 {
    match pitch_name {
        PitchName::C => 0,
        PitchName::D => 2,
        PitchName::E => 4,
        PitchName::F => 5,
        PitchName::G => 7,
        PitchName::A => 9,
        PitchName::B => 11,
    }
}

fn accidental_to_midi_pitch (accidental : Accidental) -> i64 {
    match accidental {
        Accidental::Natural => 0,
        Accidental::Sharp => 1,
        Accidental::Flat => -1,
    }
}

fn ui_pitch_to_midi_pitch (pitch_name : PitchName, accidental : Accidental, octave : u64) -> u64 {
    (pitch_name_to_midi_pitch(pitch_name) as i64 +
    accidental_to_midi_pitch(accidental)) as u64 +
    octave_to_midi_pitch(octave)
}


// check if note contains the selection, but defining a cursor that is at the start
// of the note as not containing the note.
fn note_contains_selection_ignore_start (note : &PlayerNote, selection : Selection) -> bool {
    note.x == selection.x && note.start < selection.y && note.start + note.nsteps as u64 <= selection.y
}

// check if note contains the selection, but defining a cursor that is at the end
// of the note as not containing the note.
fn note_contains_selection_ignore_end (note : &PlayerNote, selection : Selection) -> bool {
    note.x == selection.x && note.start <= selection.y && (note.start + note.nsteps as u64) < selection.y
}

// given a y location, return at most two player notes that are split at the y location.
fn player_note_split_at (note : &PlayerNote, y : u64) -> (Option<PlayerNote>, Option<PlayerNote>) {
    assert!(note.nsteps > 0);
    let end = note.start + note.nsteps as u64;

    if (y >= end) {
        // note ends before y
        return (Some(note.clone()), None);
    }
    assert!(y < end);
    if (note.start >= y) {
        return (None, Some(note.clone()));
    }
    assert!(note.start < y);
    assert!(end - note.start >= 2);
    let mut n1 = note.clone();
    n1.nsteps = (y - note.start) as i64;
    assert!(n1.nsteps > 0);
    let mut n2 = note.clone();
    n2.start = n1.start + n1.nsteps as u64;
    n2.nsteps = (end - y) as i64;
    assert!((n1.nsteps + n2.nsteps) == note.nsteps);
    return (Some(n1), Some(n2));
}

impl PlayerNote {
    pub fn pitch(&self) -> u64 {
        ui_pitch_to_midi_pitch(self.pitch_name, self.accidental, self.octave)
    }

    pub fn to_str (&self) -> String {
        format!("{}{}", self.pitch_name.to_str(), self.accidental.to_str())
    }

    pub fn y(&self) -> u64 {
        self.start
    }

    pub fn lower_octave (&mut self) {
        if self.octave > 0 {
            self.octave -= 1;
        }
    }

    pub fn raise_octave(&mut self) {
        if self.octave < 8 {
            self.octave += 1;
        }
    }

    pub fn insert_newline_at (&self, selection : Selection, accum : &mut Vec<PlayerNote>) {
        if selection.x != self.x {
            accum.push(self.clone())
        } else {
            match player_note_split_at(self, selection.y) {
                (Some(n1), None) => {
                    // stuff entirely before is unaffected.
                    accum.push(n1);
                },
                (None, Some(mut n2)) => {
                    // note is entirely to the right.
                    // if we are at the line of the note,
                    // stuff entirely after moves up.
                    n2.start += 1;
                    accum.push(n2);
                },
                (Some(n1), Some(mut n2)) => {
                    // note must be broken up, moving the lower note downward,
                    accum.push(n1);
                    n2.start += 1;
                    accum.push(n2);
                },
                (None, None) => {
                    // impossible!
                    panic!("Impossible case");
                },
            }
        }
    }

    // returns true if something of significance was consumed.
    pub fn delete_line (&self, selection : Selection, accum : &mut Vec<PlayerNote>) -> () {
        if selection.x != self.x {
            accum.push(self.clone())
        } else {
            let (n1, n2) = player_note_split_at(self, selection.y);
            match (n1, n2) {
                (Some(n1), None) => {
                    // stuff entirely before is unaffected.
                    accum.push(n1);
                },
                (Some(n1), Some(n2)) => {
                    // note must be made smaller.
                    let mut out = self.clone();
                    out.nsteps = self.nsteps - 1;
                    if (out.nsteps > 0) {
                        accum.push(out);
                    }
                }
                (None, Some(mut n2)) => {
                    // note is entirely to the right.
                    // if we are at the line of the note,
                    // stuff entirely after moves up.
                    if (n2.start > 0) {
                        n2.start -= 1;
                    }
                    accum.push(n2);
                },
                (None, None) => {
                    // impossible!
                    panic!("Impossible case");
                },
            }

        }
    }

    pub fn decrease_nsteps (&self) -> Option<PlayerNote> {
        let mut note = self.clone();
        if note.nsteps > 1 {
            note.nsteps -= 1;
            Some(note)
        } else {
            None
        }
    }

    pub fn increase_nsteps (&self) -> PlayerNote {
        let mut note = self.clone();
        // TODO: what should happen to a note with duration zero?
        note.nsteps += 1;
        note
    }
}


#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
pub struct PlayerTrack {
    // TODO: make this immutable vector with imrs
    pub notes: Vec<PlayerNote>, // sorted by start
    // TODO: make this immutable vector with imrs
    pub hitbox : HashMap<(u64, u64), usize>, // maps (x, y) to index in notes.
}

fn build_hitbox (notes : &Vec<PlayerNote>) -> HashMap<(u64, u64), usize> {
    let mut hitbox = HashMap::new();
    for (ix, note) in notes.iter().enumerate() {
        assert!(note.nsteps > 0);
        for y in note.start..note.start + note.nsteps as u64 {
            // can't have another note at the same location.
            assert!(!hitbox.contains_key(&(note.start, y)));
            hitbox.insert((note.x, y), ix);
        }
    }
    hitbox
}

impl Default for PlayerTrack {
    fn default() -> Self {
        Self::new()
    }
}

impl PlayerTrack {
    pub fn new() -> PlayerTrack {
        PlayerTrack {
            notes: Vec::new(),
            hitbox : HashMap::new()
        }
    }

    pub fn from_notes(notes : Vec<PlayerNote>) -> PlayerTrack {
        PlayerTrack {
            hitbox : build_hitbox(&notes),
            notes: notes,
        }
    }

    pub fn add_note (&mut self, note : PlayerNote) {
        self.notes.push(note);
        self.hitbox = build_hitbox(&self.notes);
    }



    pub fn get_note_from_coord (&self, x : u64, y : u64) -> Option<PlayerNote> {
        match self.hitbox.get(&(x, y)) {
            Some(ix) => Some(self.notes[*ix]),
            None => None,
        }
    }

    pub fn get_note_ix_from_coord (&self, x : u64, y : u64) -> Option<usize> {
        match self.hitbox.get(&(x, y)) {
            Some(ix) => Some(*ix),
            None => None,
        }
    }

    pub fn modify_note_at_ix_mut (&mut self, ix : usize, f : impl FnOnce(&mut PlayerNote)) {
        assert!(ix < self.notes.len());
        f(&mut self.notes[ix]);
        self.hitbox = build_hitbox(&self.notes);
    }

    pub fn get_note_from_coord_mut (&mut self, x : u64, y : u64) -> Option<&mut PlayerNote> {
        match self.hitbox.get(&(x, y)) {
            Some(ix) => Some(&mut self.notes[*ix]),
            None => None,
        }
    }

    pub fn get_last_instant (&self) -> u64 {
        self.notes.iter().map(|note| note.start + note.nsteps as u64).max().unwrap_or(0)
    }

    fn insert_newline (&mut self, selection : Selection) {
        let mut new_notes = Vec::new();
        for note in self.notes.iter() {
            note.insert_newline_at(selection, &mut new_notes);
        }
        self.notes = new_notes;
        self.hitbox = build_hitbox(&self.notes);
    }

    fn delete_line (&mut self, selection : Selection) {
        let mut new_notes = Vec::new();
        for note in self.notes.iter() {
            note.delete_line(selection, &mut new_notes);
        }
        self.notes = new_notes;
        self.hitbox = build_hitbox(&self.notes);
    }

    fn delete_note (&mut self, selection : Selection) {
        if let Some(ix) = self.hitbox.get(&(selection.x, selection.y)) {
            self.notes.remove(*ix);
            // TODO: optimize?
            self.hitbox = build_hitbox(&self.notes);
        }
    }

    fn increase_nsteps (&mut self, selection : Selection) {
        if let Some(ix) = self.hitbox.get(&(selection.x, selection.y)) {
            let note = self.notes[*ix];

            // do we need to make space for more notes? yes we do!
            for bumpedNote in self.notes.iter_mut() {
                // the other note starts at or after the note we just bumped,
                // so we need to push it down to make space for it!
                if bumpedNote.x == selection.x &&  bumpedNote.start >= note.start + note.nsteps as u64 {
                    bumpedNote.start += 1;
                }
            }


            // now that we've made space, adjust the current note.
            self.notes[*ix] = note.increase_nsteps();
            self.hitbox = build_hitbox(&self.notes)
        }
    }

    fn decrease_nsteps (&mut self, selection : Selection) {
        if let Some(ix) = self.hitbox.get(&(selection.x, selection.y)) {
            let note = self.notes[*ix];

            // we need to delete space that was occupied by this note.
            for bumpedNote in self.notes.iter_mut() {
                // the other note starts at or after the note we just bumped,
                // so we need to push it down to make space for it!
                if bumpedNote.x == selection.x &&
                    bumpedNote.start >= note.start + note.nsteps as u64 {
                    bumpedNote.start -= 1;
                }
            }

            if let Some(newNote) = note.decrease_nsteps() {
                self.notes[*ix] = newNote; // we've decreased the duration of this note.
            } else {
                // we've deleted this note.
                // TODO: keep this around, until someone tells us that the increase/decrease manipulation
                // has ended, at which point we can delete the tombstone values.
                self.notes.remove(*ix);
            }
            self.hitbox = build_hitbox(&self.notes)
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
    pub fn to_str(&self) -> &str {
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

    pub fn to_lean(&self) -> u64 {
        match self {
            PitchName::C => 0,
            PitchName::D => 1,
            PitchName::E => 2,
            PitchName::F => 3,
            PitchName::G => 4,
            PitchName::A => 5,
            PitchName::B => 6,
        }
    }

    pub fn of_lean (ix : u64) -> PitchName {
        match ix {
            0 => PitchName::C,
            1 => PitchName::D,
            2 => PitchName::E,
            3 => PitchName::F,
            4 => PitchName::G,
            5 => PitchName::A,
            6 => PitchName::B,
            _ => panic!("Invalid pitch name index {}", ix),
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
    pub fn to_str(&self) -> &str {
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
            y: 0,
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
enum Action {
    CursorMoveLeftOne,
    CursorMoveRightOne,
    CursorMoveDownOne,
    CursorMoveUpOne,
    ToggleSharp,
    ToggleFlat,
    Newline,
    DeleteLine,
    DeleteNote,
    LowerOctave,
    RaiseOctave,
    IncreaseNSteps,
    DecreaseNSteps,
}

#[derive (Debug, PartialEq, Serialize, Deserialize, Clone)]
struct History {
    actions : Vec<(Action, Selection, PlayerTrack)>,
    current : usize,
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

#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct Context {
    pub file_path : PathBuf,
    pub track : PlayerTrack,
    pub selection : Selection,
    pub playback_speed : f64,
    pub track_name : String,
    pub artist_name : String,
    pub time_signature : (u8, u8),
    pub history : History,
}


impl Context {
    // TODO: take egui context to set title.
    pub fn new(file_path : PathBuf) -> Context {
        Context {
            file_path,
            track: PlayerTrack::new(),
            selection: Selection::new(),
            playback_speed: 1.0,
            track_name: "Untitled".to_string(),
            artist_name: "Unknown".to_string(),
            time_signature: (4, 4),
            history: History::new(),
        }

    }


    pub fn get_midi_export_file_path(&self) -> PathBuf {
        let mut out = self.file_path.clone();
        out.set_extension(".mid");
        out
    }

    pub fn set_pitch (&mut self, pitch : PitchName) {
        // if a note exists, set its pitch.
        if let Some(note) = self.track.get_note_from_coord_mut(self.selection.x, self.selection.y) {
            note.pitch_name = pitch;
        }
        // otherwise, add a note.
        self.track.add_note(PlayerNote {
            x: self.selection.x,
            start: self.selection.y,
            nsteps: 1,
            pitch_name: pitch,
            accidental: Accidental::Natural,
            octave: 4,
        });
    }

    pub fn cursor_move_left_one (&mut self) {
        self.history.push(Action::CursorMoveLeftOne, self.selection, self.track.clone());
        self.selection = self.selection.move_left_one();
    }

    pub fn cursor_move_right_one (&mut self) {
        self.history.push(Action::CursorMoveRightOne, self.selection, self.track.clone());
        self.selection = self.selection.move_right_one();
    }

    pub fn cursor_move_down_one (&mut self) {
        self.history.push(Action::CursorMoveDownOne, self.selection, self.track.clone());
        self.selection = self.selection.move_down_one();
    }

    pub fn cursor_move_up_one (&mut self) {
        self.history.push(Action::CursorMoveUpOne, self.selection, self.track.clone());
        self.selection = self.selection.move_up_one();
    }

    pub fn toggle_sharp (&mut self) {
        if let Some(ix) = self.track.get_note_ix_from_coord(self.selection.x, self.selection.y) {
            self.history.push(Action::ToggleSharp, self.selection, self.track.clone());
            self.track.modify_note_at_ix_mut(ix, |note| {
                note.accidental = note.accidental.toggle_sharp()
            });
        }
    }

    pub fn toggle_flat (&mut self) {
        if let Some(ix) = self.track.get_note_ix_from_coord(self.selection.x, self.selection.y) {
            self.history.push(Action::ToggleFlat, self.selection, self.track.clone());
            self.track.modify_note_at_ix_mut(ix, |note| {
                note.accidental = note.accidental.toggle_flat()
            });
        }
    }

    pub fn newline (&mut self) {
        self.history.push(Action::Newline, self.selection, self.track.clone());
        self.track.insert_newline(self.selection);
        self.selection = self.selection.move_down_one();
    }

    pub fn delete_line (&mut self) {
        self.history.push(Action::DeleteLine, self.selection, self.track.clone());
        self.track.delete_line(self.selection);
        self.selection = self.selection.move_up_one();
    }

    pub fn delete_note (&mut self) {
        self.track.delete_note(self.selection);
        self.selection = self.selection.move_up_one();
        self.history.push(Action::DeleteNote, self.selection, self.track.clone());
    }

    pub fn lower_octave (&mut self) {
        if let Some(ix) = self.track.get_note_ix_from_coord(self.selection.x, self.selection.y) {
            self.history.push(Action::LowerOctave, self.selection, self.track.clone());
            self.track.modify_note_at_ix_mut(ix, |note| {
                note.lower_octave()
            });
        }
    }

    pub fn raise_octave (&mut self) {
        if let Some(ix) = self.track.get_note_ix_from_coord(self.selection.x, self.selection.y) {
            self.history.push(Action::RaiseOctave, self.selection, self.track.clone());
            self.track.modify_note_at_ix_mut(ix, |note| {
                note.raise_octave()
            });
        }
    }

    pub fn increase_nsteps (&mut self) {
        self.history.push(Action::IncreaseNSteps, self.selection, self.track.clone());
        self.track.increase_nsteps(self.selection);
    }

    pub fn decrease_nsteps (&mut self) {
        self.history.push(Action::DecreaseNSteps, self.selection, self.track.clone());
        self.track.decrease_nsteps(self.selection);
    }

    pub fn undo_action (&mut self) {
        match self.history.undo() {
            Some((action, selection, track)) => {
                self.selection = selection;
                self.track = track;
            },
            None => {
                event!(Level::INFO, "No more actions to undo");
            }
        }
    }

    pub fn redo_action (&mut self) {
        match self.history.redo() {
            Some((action, selection, track)) => {
                self.selection = selection;
                self.track = track;
            },
            None => {
                event!(Level::INFO, "No more actions to redo");
            }
        }
    }
    pub fn get_app_title(&self) -> String {
        format!("monodrone({})", self.file_path.file_name().unwrap().to_string_lossy())
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
                self.time_signature.0.into(), // numerator: 4,
                self.time_signature.1.into(), // denominator: 4,
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
        let TIME_DELTA : u32 = (256.0 / self.playback_speed) as u32;
        let mut time_delta_accum = 0;
        for t in 0..max_time+1 {
            time_delta_accum += TIME_DELTA; // for this instant of time, add time.
            let player_notes = track_get_note_events_at_time(&self.track, t);
            for (i, player_note) in player_notes.iter().enumerate() {
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

impl Clone for Context {
    fn clone(&self) -> Self {
        Context {
            file_path: self.file_path.clone(),
            track: self.track.clone(),
            selection: self.selection.clone(),
            playback_speed: self.playback_speed,
            track_name: self.track_name.clone(),
            artist_name: self.artist_name.clone(),
            time_signature: self.time_signature,
            history: self.history.clone(),
        }
    }
}
