
use std::{collections::HashMap, path::PathBuf};
use lean_sys::{lean_box, lean_dec_ref, lean_inc_ref, lean_io_result_get_error, lean_object, lean_unbox_float};

use tracing::{event, Level};

use crate::{track_get_note_events_at_time};

pub struct LeanPtr {
    ptr : *mut lean_object,
}

impl LeanPtr {
    // take ownership of lean pointer.
    pub fn take (ptr : *mut lean_object) -> LeanPtr {
        LeanPtr { ptr }
    }
    pub fn run<F, O> (&mut self, f : F) -> O where F : FnOnce(*mut lean_object) -> O {
        unsafe {
            lean_inc_ref(self.ptr);
        }
        f(self.ptr)
    }

    // consumes this pointer and returns a new one, with the value updated according to the function.
    pub fn update<F> (self, f : F) -> LeanPtr where F : FnOnce(*mut lean_object) -> *mut lean_object{
        LeanPtr {
            ptr : f(self.ptr)
        }
    }
}

impl Drop for LeanPtr {
    fn drop(&mut self) {
        unsafe {
            lean_dec_ref(self.ptr);
        }
    }
}

impl Clone for LeanPtr {
    fn clone(&self) -> Self {
        unsafe {
            lean_inc_ref(self.ptr);
        }
        LeanPtr { ptr : self.ptr }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct PlayerNote {
    pub pitch: u64,
    pub start: u64,
    pub nsteps: u64,
}


#[derive(Debug, Clone, PartialEq)]
pub struct PlayerTrack {
    pub notes: Vec<PlayerNote>, // sorted by start
}

impl Default for PlayerTrack {
    fn default() -> Self {
        Self::new()
    }
}

impl PlayerTrack {
    pub fn new() -> PlayerTrack {
        PlayerTrack { notes: Vec::new() }
    }

}



#[derive(Debug, Clone, PartialEq)]
pub struct TrackBuilder {
    notes: Vec<PlayerNote>,
    time : u64,
}
impl Default for TrackBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl TrackBuilder {
    pub fn new() -> TrackBuilder {
        TrackBuilder { notes: Vec::new(), time: 0 }
    }

    /// Add a note to the track that is held for `nsteps` steps.
    pub fn note_held(&mut self, pitch: u64, nsteps: u64) -> &mut Self {
        self.notes.push(PlayerNote { pitch, start: self.time, nsteps });
        self.time += nsteps;
        self
    }

    /// Add a note to the track that is held for 1 step.
    pub fn note1(&mut self, pitch: u64) -> &mut Self {
        self.note_held(pitch, 1)
    }

    /// Add a note to the track that is held for 1 step.
    pub fn note8(&mut self, pitch: u64) -> &mut Self {
        self.note_held(pitch, 8)
    }


    /// Add a rest to the track of `nsteps` steps.
    pub fn rest(&mut self, nsteps: u64) -> &mut Self {
        self.time += nsteps;
        self
    }

    pub fn build(&self) -> PlayerTrack {
        PlayerTrack { notes: self.notes.clone() }
    }
}


impl From<TrackBuilder> for PlayerTrack {
    fn from(builder: TrackBuilder) -> Self {
        PlayerTrack { notes: builder.notes }
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


#[derive(Debug, Clone, Copy, PartialEq)]
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

#[derive(Debug, Clone, Copy, PartialEq)]
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
}

#[derive(Debug, PartialEq)]
pub struct UINote {
    pub pitch_name: PitchName,
    pub accidental : Accidental,
    pub x: u64,
    pub octave : u64,
    pub y: u64,
    pub nsteps: u64,
}

impl UINote {
    pub fn to_str (&self) -> String {
        format!("{}{}", self.pitch_name.to_str(), self.accidental.to_str())
    }
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
    (pitch_name_to_midi_pitch(pitch_name) as i64 + accidental_to_midi_pitch(accidental)) as u64 + octave_to_midi_pitch(octave)
}

impl UINote {
    pub fn from_lean (note : *mut lean_object) -> UINote {
        let pitch_name = unsafe { monodrone_ctx_run_linear_fn(note, monodrone_note_get_pitch_name) };
        let x = unsafe { monodrone_ctx_run_linear_fn(note, monodrone_note_get_x) };
        let y = unsafe { monodrone_ctx_run_linear_fn(note, monodrone_note_get_y) };
        let nsteps = unsafe { monodrone_ctx_run_linear_fn(note, monodrone_note_get_nsteps) };
        let octave = unsafe { monodrone_ctx_run_linear_fn(note, monodrone_note_get_octave) };
        let accidental = unsafe { monodrone_ctx_run_linear_fn(note, monodrone_note_get_accidental) };
        UINote { pitch_name: PitchName::of_lean(pitch_name),
            accidental: Accidental::of_lean(accidental),
            octave,
            x, y,
            nsteps }
    }

    pub fn to_player_note (&self) -> PlayerNote {
        PlayerNote { pitch: ui_pitch_to_midi_pitch(self.pitch_name, self.accidental, self.octave) ,
            start: self.y, nsteps: self.nsteps }
    }
}

impl Clone for UINote {
    fn clone(&self) -> Self {
        UINote { pitch_name: self.pitch_name,
            accidental: self.accidental,
            x: self.x,
            octave: self.octave,
            y: self.y,
            nsteps: self.nsteps,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct UITrack {
    pub sync_index: u64,
    pub notes: Vec<UINote>,
    pub hitbox : HashMap<(u64, u64), usize>, // maps (x, y) to index in notes.
}

impl UITrack {
    pub fn from_lean (ctx : *mut lean_object) -> UITrack {
        let len: u64 = unsafe {
            monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_get_track_length)
        };
        let mut notes: Vec<UINote> = Vec::new();
        for i in 0..len {
            unsafe {
                lean_inc_ref(ctx);
                let note  = monodrone_ctx_get_track_note(ctx, i);
                notes.push(UINote::from_lean(note));
            }
        }

        let mut hitbox = HashMap::new();
        for (ix, note) in notes.iter().enumerate() {
            for y in note.y..note.y + note.nsteps {
                hitbox.insert((note.x, y), ix);
            }
        }

        let sync_index = unsafe {
            monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_get_track_sync_index)
        };

        UITrack { sync_index, notes, hitbox }
    }

    pub fn get_note_from_coord (&self, x : u64, y : u64) -> Option<&UINote> {
        match self.hitbox.get(&(x, y)) {
            Some(ix) => Some(&self.notes[*ix]),
            None => None,
        }
    }

    pub fn to_player_track (&self) -> PlayerTrack {
        let mut notes = Vec::new();
        for note in &self.notes {
            notes.push(note.to_player_note());
        }
        PlayerTrack { notes }
    }

    pub fn get_last_instant (&self) -> u64 {
        self.notes.iter().map(|note| note.y + note.nsteps).max().unwrap_or(0)
    }
}


const NTRACKS : u32 = 4;
const TRACK_LENGTH : u32 = 100;


#[derive(Debug, Clone, PartialEq)]
pub struct Selection {
    pub cursor : egui::Pos2,
    pub x : u32,
    pub y : u32,
}


impl Selection {

    fn new(&self) -> Selection {
        Selection {
            cursor: egui::vec2(0.0, 0.0),
            x: 0,
            y: 0,
        }
    }

    fn move_left_one(&self) -> Selection {
        Selection {
            cursor: self.cursor - egui::vec2(1.0, 0.0),
            x : (self.x - 1).clamp(0, NTRACKS - 1),
            y : self.y
        }
    }

    fn move_right_one(&self) -> Selection {
        Selection {
            cursor: self.cursor + egui::vec2(1.0, 0.0),
            x : (self.x + 1).clamp(0, NTRACKS - 1),
            y : self.y
        }
    }

    fn move_down_one(&self) -> Selection {
        Selection {
            cursor: self.cursor + egui::vec2(0.0, 1.0),
            x : self.x,
            y : (self.y + 1).clamp(0, TRACK_LENGTH - 1),
        }
    }

    fn move_up_one(&self) -> Selection {
        Selection {
            cursor: (self.cursor - egui::vec2(0.0, 1.0)),
            x : self.x,
            y : (self.y - 1).clamp(0, TRACK_LENGTH - 1),
        }
    }



}
pub struct Context {
    file_path : PathBuf,
    track : UITrack,
    selection : Selection,
    playback_speed : f64,
    track_name : String,
    artist_name : String,
    time_signature : (u8, u8),
}

impl Context {
    // TODO: take egui context to set title.
    pub fn new(file_path : PathBuf) -> Context {
        let ctx = new_context(file_path.as_path().to_str().unwrap());
        Context::from_raw_ctx(ctx, file_path)
    }

    pub fn from_raw_ctx (ctx : *mut lean_object, file_path : PathBuf) -> Context {
        let track = UITrack::from_lean(ctx);
        let selection = Selection::new(ctx);
        event!(Level::INFO, "track: {:?}", track);
        event!(Level::INFO, "selection: {:?}", selection);
        Context {
            file_path, // TODO: store state on Lean side.
            // ctx,
            track,
            selection,
            playback_speed: get_playback_speed(ctx),
            track_name: get_track_name(ctx),
            artist_name: get_artist_name(ctx),
            time_signature: (get_time_signature_fst(ctx), get_time_signature_snd(ctx)),
         }
    }

    pub fn get_track_name (&self) -> &str {
        &self.track_name
    }

    pub fn get_track_name_mut (&mut self) -> &mut String {
        &mut self.track_name
    }

    pub fn get_artist_mut (&mut self) -> &mut String {
        &mut self.artist_name
    }

    pub fn get_time_signature_mut (&mut self) -> &mut (u8, u8) {
        &mut self.time_signature
    }


    pub fn track(&self) -> &UITrack {
        &self.track
    }

    pub fn selection(&self) -> &Selection {
        &self.selection
    }

    pub fn file_path(&self) -> &PathBuf {
        &self.file_path
    }

    pub fn set_playback_speed(&mut self, value : f64) {
        self.playback_speed = value;
    }

    pub fn to_json_string(&self) -> String {
        // TODO: convert o json string.
        // ctx_to_json_string(self.ctx)
        panic!("Not implemented");
    }

    pub fn get_midi_export_file_path(&self) -> PathBuf {
        let mut out = self.file_path.clone();
        out.set_extension(".mid");
        out
    }

    pub fn set_pitch (&mut self, pitch : PitchName) {
        panic!("Not implemented");
        // self.run_ctx_fn(|ctx| set_pitch(ctx, pitch))
    }

    pub fn cursor_move_left_one (&mut self) {
        self.selection = self.selection.move_left_one();
    }

    pub fn cursor_move_right_one (&mut self) {
        self.selection = self.selection.move_right_one();
    }

    pub fn cursor_move_down_one (&mut self) {
        self.selection = self.selection.move_down_one();
    }

    pub fn cursor_move_up_one (&mut self) {
        self.selection = self.selection.move_up_one();
    }

    pub fn toggle_sharp (&mut self) {
        panic!("Not implemented");
    }

    pub fn toggle_flat (&mut self) {
        panic!("Not implemented");
    }

    pub fn newline (&mut self) {
        panic!("Not implemented");
    }

    pub fn delete_line (&mut self) {
        panic!("Not implemented");
    }

    pub fn delete_note (&mut self) {
        panic!("Not implemented");
    }

    pub fn lower_octave (&mut self) {
        panic!("Not implemented");
    }

    pub fn raise_octave (&mut self) {
        panic!("Not implemented");
    }

    pub fn increase_nsteps (&mut self) {
        panic!("Not implemented");
    }

    pub fn decrease_nsteps (&mut self) {
        panic!("Not implemented");
    }

    pub fn undo_action (&mut self) {
        panic!("Not implemented");
    }

    pub fn redo_action (&mut self) {
        panic!("Not implemented");
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
        let player_track = self.track().to_player_track();
        for note in player_track.notes.iter() {
            let end = note.start + note.nsteps;
            max_time = max_time.max(end);
        }
        let TIME_DELTA : u32 = (256.0 / self.playback_speed) as u32;
        let mut time_delta_accum = 0;
        for t in 0..max_time+1 {
            time_delta_accum += TIME_DELTA; // for this instant of time, add time.
            let player_notes = track_get_note_events_at_time(&player_track, t);
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
        }
    }
}
