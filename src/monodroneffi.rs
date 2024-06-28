
use std::{collections::HashMap, path::PathBuf};
use lean_sys::{lean_box, lean_dec_ref, lean_inc, lean_inc_ref, lean_initialize_runtime_module, lean_io_mark_end_initialization, lean_io_result_get_error, lean_io_result_get_value, lean_io_result_is_error, lean_mk_io_user_error, lean_object, lean_unbox_float};
use midly;
use lean_sys;
use tracing::{event, Level};

use crate::{track_get_note_events_at_time, NoteEvent};

extern {
    pub fn initialize_Monodrone(builtin : u8, world : *mut lean_object) -> lean_object;

    // ctx.
    fn monodrone_ctx_new (path : *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_step (ctx : *mut lean_object) -> *mut lean_object;

    // cursor movement.
    fn monodrone_ctx_cursor_move_left_one(ctx: *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_cursor_move_right_one(ctx: *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_cursor_move_down_one(ctx: *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_cursor_move_up_one(ctx: *mut lean_object) -> *mut lean_object;

    // selection movement.
    fn monodrone_ctx_select_anchor_move_left_one(ctx: *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_select_anchor_move_right_one(ctx: *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_select_anchor_move_down_one(ctx: *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_drag_down_one(ctx: *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_drag_up_one(ctx: *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_select_anchor_move_up_one(ctx: *mut lean_object) -> *mut lean_object;
    // note editing.
    fn monodrone_ctx_set_pitch(ctx : *mut lean_object, pitch : u64) -> *mut lean_object;
    fn monodrone_ctx_toggle_sharp(ctx : *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_toggle_flat(ctx : *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_lower_octave (ctx : *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_raise_octave (ctx : *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_newline (ctx : *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_delete_note (ctx : *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_delete_line (ctx : *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_set_nsteps (ctx : *mut lean_object, nsteps : u64) -> *mut lean_object;
    fn monodrone_ctx_increase_nsteps (ctx : *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_decrease_nsteps (ctx : *mut lean_object) -> *mut lean_object;

    // fn monodrone_copy(ctx : *mut lean_object);
    // fn monodrone_paste(ctx : *mut lean_object);


    // cursor query
    fn monodrone_ctx_get_cursor_sync_index(ctx : *mut lean_object) -> u64;
    fn monodrone_ctx_get_cursor_x(ctx : *mut lean_object) -> u64;
    fn monodrone_ctx_get_cursor_y(ctx : *mut lean_object) -> u64;

    // selection query
    // fn monodrone_ctx_has_select_anchor (ctx : *mut lean_object) -> bool;
    fn monodrone_ctx_get_select_anchor_x (ctx : *mut lean_object) -> u64;
    fn monodrone_ctx_get_select_anchor_y (ctx : *mut lean_object) -> u64;


    // track query
    fn monodrone_ctx_get_track_sync_index(ctx : *mut lean_object) -> u64;
    fn monodrone_ctx_get_track_length(ctx : *mut lean_object) -> u64;
    fn monodrone_ctx_get_track_note(ctx : *mut lean_object, i : u64) -> *mut lean_object;

    // note query
    fn monodrone_note_get_pitch_name(note : *mut lean_object) -> u64;
    fn monodrone_note_get_accidental(note : *mut lean_object) -> u64;
    fn monodrone_note_get_x(note : *mut lean_object) -> u64;
    fn monodrone_note_get_y(note : *mut lean_object) -> u64;
    fn monodrone_note_get_nsteps(note : *mut lean_object) -> u64;
    fn monodrone_note_get_octave (note : *mut lean_object) -> u64;

    // Undo/Redo action
    fn monodrone_ctx_undo_action(ctx : *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_redo_action(ctx : *mut lean_object) -> *mut lean_object;

    // Undo/Redo movement
    fn monodrone_ctx_undo_movement (ctx : *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_redo_movement (ctx : *mut lean_object) -> *mut lean_object;

    fn monodrone_ctx_to_json_str (ctx : *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_from_json_str (json_str : *mut lean_object) -> *mut lean_object;


    fn monodrone_ctx_get_playback_speed_sequence_number (ctx : *mut lean_object) -> u64;
    fn monodrone_ctx_get_playback_speed (ctx : *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_set_playback_speed (ctx : *mut lean_object, speed : *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_increase_playback_speed (ctx : *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_decrease_playback_speed (ctx : *mut lean_object) -> *mut lean_object;

    fn lean_io_error_to_string (io_obj : *mut lean_object) -> *mut lean_object;
}

/// Run a function that is linear in the monodrone ctx, so we bump the ref count once and then call the function.
pub fn monodrone_ctx_run_linear_fn<T> (ctx : *mut lean_object, f : unsafe extern "C" fn(*mut lean_object) -> T) -> T {
    unsafe {
        lean_inc_ref(ctx);
        f(ctx)
    }
}

// consumes the string.
pub fn lean_str_to_String (lean_str : *mut lean_object) -> String {
    let c_str = unsafe { lean_sys::lean_string_cstr(lean_str) };
    let str = unsafe { std::ffi::CStr::from_ptr(c_str as *const i8).to_str().unwrap().to_string() };
    unsafe { lean_sys::lean_dec_ref(lean_str); }
    str
}

pub fn String_to_lean_str (string : String) -> *mut lean_object {
    let c_str = std::ffi::CString::new(string).unwrap();
    unsafe { lean_sys::lean_mk_string(c_str.to_bytes().as_ptr() as *const u8) }
}

pub fn str_to_lean_str (string : &str) -> *mut lean_object {
    let c_str = std::ffi::CString::new(string).unwrap();
    unsafe { lean_sys::lean_mk_string(c_str.to_bytes().as_ptr() as *const u8) }
}


// # Ctx function wrappers.
pub fn initialize() -> () {
    unsafe { initialize_Monodrone(1, lean_box(0)) };
}
pub fn new_context(path : &str) -> *mut lean_object {
    unsafe { monodrone_ctx_new(str_to_lean_str(path)) }
}

// cursor movement.
pub fn cursor_move_left_one(ctx: *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_cursor_move_left_one) }

}
pub fn cursor_move_right_one(ctx: *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_cursor_move_right_one) }
}
pub fn cursor_move_down_one(ctx: *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_cursor_move_down_one) }
}
pub fn cursor_move_up_one(ctx: *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_cursor_move_up_one) }
}

pub fn select_anchor_move_left_one(ctx: *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_select_anchor_move_left_one) }
}

pub fn select_anchor_move_right_one(ctx: *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_select_anchor_move_right_one) }
}

pub fn select_anchor_move_down_one(ctx: *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_select_anchor_move_down_one) }
}

pub fn drag_down_one(ctx: *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_drag_down_one) }
}

pub fn drag_up_one(ctx: *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_drag_up_one) }
}

pub fn select_anchor_move_up_one(ctx: *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_select_anchor_move_up_one) }
}

// note editing.
pub fn set_pitch(ctx : *mut lean_object, pitch : PitchName) -> *mut lean_object {
    unsafe { lean_inc_ref(ctx); }
    unsafe { monodrone_ctx_set_pitch(ctx, pitch.to_lean() ) }
}

pub fn toggle_sharp (ctx : *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_toggle_sharp) }
}

pub fn toggle_flat (ctx : *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_toggle_flat) }
}

pub fn lower_octave (ctx : *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_lower_octave) }
}

pub fn raise_octave (ctx : *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_raise_octave) }
}


pub fn get_track_sync_index (ctx : *mut lean_object) -> u64 {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_get_track_sync_index) }
}

pub fn get_cursor_sync_index (ctx : *mut lean_object) -> u64 {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_get_cursor_sync_index) }
}




pub fn step (ctx : *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_step) }
}

pub fn undo_action (ctx : *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_undo_action) }
}

pub fn redo_action (ctx : *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_redo_action) }
}

pub fn newline (ctx : *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_newline) }
}

pub fn delete_note (ctx : *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_delete_note) }
}

pub fn delete_line (ctx : *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_delete_line) }
}

pub fn set_nsteps (ctx : *mut lean_object, nsteps : u64) -> *mut lean_object {
    unsafe {
        lean_inc_ref(ctx);
        monodrone_ctx_set_nsteps(ctx, nsteps)
    }
}
pub fn increase_nsteps (ctx : *mut lean_object) -> *mut lean_object {
    unsafe {
        monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_increase_nsteps)
    }
}

pub fn decrease_nsteps (ctx : *mut lean_object) -> *mut lean_object {
    unsafe {
        monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_decrease_nsteps)
    }
}


pub fn ctx_to_json_string (ctx : *mut lean_object) -> String {
    unsafe {
        let lean_str = monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_to_json_str);
        let str = lean_str_to_String(lean_str);
        return str;
    }
}

// TODO: implement Result.
pub fn ctx_from_json_str (string : String) -> Result<*mut lean_object, String> {
    let lean_str = String_to_lean_str(string);
    let io_ctx = unsafe { monodrone_ctx_from_json_str(lean_str) };
    print!("io_ctx: {:p}\n", io_ctx);
    unsafe {
        lean_inc_ref(io_ctx);
        if lean_sys::lean_io_result_is_ok(io_ctx) {
            let ctx = lean_sys::lean_io_result_get_value(io_ctx);
            print!("ctx: {:p}\n", ctx);
            return Ok(ctx);
        } else {
            let err = lean_io_result_get_error(io_ctx);
            let err_str = lean_str_to_String(lean_io_error_to_string(err));
            return Err(err_str);
        }
    }
}

pub fn get_playback_speed (ctx : *mut lean_object) -> f64 {
    unsafe {
        let obj =  monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_get_playback_speed);
        let out = lean_unbox_float(obj);
        lean_dec_ref(obj);
        out
    }

}

pub fn set_playback_speed (ctx : *mut lean_object, value : f64) -> *mut lean_object {
    unsafe {
        lean_inc_ref(ctx);
        monodrone_ctx_set_playback_speed(ctx, lean_sys::lean_box_float(value))
    }

}

pub fn increase_playback_speed (ctx : *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_increase_playback_speed) }


}
pub fn decrease_playback_speed (ctx : *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_decrease_playback_speed) }


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

impl PlayerTrack {
    pub fn to_smf(&self) -> (midly::Header, Vec<midly::Track>) {
        let header = midly::Header {
            format: midly::Format::Parallel,
            timing: midly::Timing::Metrical(midly::num::u15::from_int_lossy(480)),
        };

        let mut meta_track = midly::Track::new();
        meta_track.push(midly::TrackEvent {
            delta: 0.into(),
            kind: midly::TrackEventKind::Meta(midly::MetaMessage::TrackName("Wikipedia MIDI (extended)".as_bytes())),
        });
        meta_track.push(midly::TrackEvent {
            delta: 0.into(),
            kind: midly::TrackEventKind::Meta(midly::MetaMessage::Tempo(midly::num::u24::from_int_lossy(500000))),
        });
        meta_track.push(midly::TrackEvent {
            delta: 0.into(),
            kind: midly::TrackEventKind::Meta(midly::MetaMessage::TimeSignature(
                4, // numerator: 4,
                4, // denominator: 4,
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
            kind: midly::TrackEventKind::Meta(midly::MetaMessage::TrackName("Bass".as_bytes())),
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
        for note in &self.notes {
            let start = note.start;
            let end = note.start + note.nsteps;
            max_time = max_time.max(end);
        }
        let TIME_DELTA : u32 = 120;
        for t in 0..max_time+1 {
            let player_notes = track_get_note_events_at_time(&self, t);
            // vv why does it think it's borrowed lol?
            // TODO: figure out why I need a clone()
            for (i, player_note) in player_notes.iter().enumerate() {
                let time_delta = (if i == 0 { TIME_DELTA } else { 0 }).into();
                let midi_message = player_note.to_midi_message();
                let midi_note = midly::TrackEventKind::Midi {
                    channel : 0.into(),
                    message : midi_message
                };
                track.push(midly::TrackEvent {
                    delta: time_delta,
                    kind: midi_note
                });
            }
        };

        track.push(midly::TrackEvent {
            delta: 0.into(),
            kind: midly::TrackEventKind::Meta(midly::MetaMessage::EndOfTrack),
        });
        return (header.clone(), vec![meta_track, track]);
    }
}



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

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct UINote {
    pub pitchName: PitchName,
    pub accidental : Accidental,
    pub x: u64,
    pub octave : u64,
    pub y: u64,
    pub nsteps: u64,

}

impl UINote {
    pub fn to_str (&self) -> String {
        format!("{}{}", self.pitchName.to_str(), self.accidental.to_str())
    }
}

fn octave_to_midi_pitch (octave : u64) -> u64 {
    12 * (octave + 1)
}

fn pitch_name_to_midi_pitch (pitchName : PitchName) -> u64 {
    match pitchName {
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

fn ui_pitch_to_midi_pitch (pitchName : PitchName, accidental : Accidental, octave : u64) -> u64 {
    (pitch_name_to_midi_pitch(pitchName) as i64 + accidental_to_midi_pitch(accidental)) as u64 + octave_to_midi_pitch(octave)
}

impl UINote {
    pub fn from_lean (note : *mut lean_object) -> UINote {
        let pitchName = unsafe { monodrone_ctx_run_linear_fn(note, monodrone_note_get_pitch_name) };
        let x = unsafe { monodrone_ctx_run_linear_fn(note, monodrone_note_get_x) };
        let y = unsafe { monodrone_ctx_run_linear_fn(note, monodrone_note_get_y) };
        let nsteps = unsafe { monodrone_ctx_run_linear_fn(note, monodrone_note_get_nsteps) };
        let octave = unsafe { monodrone_ctx_run_linear_fn(note, monodrone_note_get_octave) };
        let accidental = unsafe { monodrone_ctx_run_linear_fn(note, monodrone_note_get_accidental) };
        UINote { pitchName: PitchName::of_lean(pitchName),
            accidental: Accidental::of_lean(accidental),
            octave : octave,
            x, y,
            nsteps }
    }

    pub fn to_player_note (&self) -> PlayerNote {
        PlayerNote { pitch: ui_pitch_to_midi_pitch(self.pitchName, self.accidental, self.octave) ,
            start: self.y, nsteps: self.nsteps }
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

#[derive(Debug, Clone, PartialEq)]
pub struct Selection {
    pub sync_index: u64,
    pub cursor : egui::Pos2,
}

impl Selection {
    pub fn from_lean (ctx : *mut lean_object) -> Selection {

        let cursor = egui::Pos2::new(unsafe {
            monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_get_cursor_x)
        } as f32,
        unsafe {
            monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_get_cursor_y)
        } as f32);

        let sync_index = unsafe {
            monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_get_cursor_sync_index)
         };

        Selection {
            sync_index,
             cursor
        }
    }

    pub fn is_cursored(&self, pos : egui::Pos2) -> bool {
        pos == self.cursor
    }

    // pub fn is_selected (&self, x : u64, y : u64) -> bool {
    //     let min_x = self.anchor_x.min(self.cursor_x);
    //     let max_x = self.anchor_x.max(self.cursor_x);
    //     let min_y = self.anchor_y.min(self.cursor_y);
    //     let max_y = self.anchor_y.max(self.cursor_y);
    //     x >= min_x && x <= max_x && y >= min_y && y <= max_y
    // }


}


pub struct Context {
    // file_path : AppFilePath,
    file_path : PathBuf,
    ctx : *mut lean_object,
    track : UITrack,
    selection : Selection,
    playback_speed : f64,
}

impl Context {
    // TODO: take egui context to set title.
    pub fn new(file_path : PathBuf) -> Context {
        let ctx = new_context(&file_path.as_path().to_str().unwrap());
        Context::from_raw_ctx(ctx, file_path)
    }

    pub fn from_raw_ctx (ctx : *mut lean_object, file_path : PathBuf) -> Context {
        let track = UITrack::from_lean(ctx);
        let selection = Selection::from_lean(ctx);
        event!(Level::INFO, "track: {:?}", track);
        event!(Level::INFO, "selection: {:?}", selection);
        Context {
            file_path: PathBuf::new(), // TODO: store state on Lean side.
            ctx,
            track,
            selection,
            playback_speed: get_playback_speed(ctx),
         }
    }

    pub fn run_ctx_fn<F> (&mut self, f : F) where F : FnOnce(*mut lean_object) -> *mut lean_object {
        self.ctx = unsafe {
            lean_inc_ref(self.ctx);
            f(self.ctx)
        };

        if self.track.sync_index != unsafe { monodrone_ctx_run_linear_fn(self.ctx, monodrone_ctx_get_track_sync_index) } {
            self.track = UITrack::from_lean(self.ctx);
        }

        if self.selection.sync_index != unsafe { monodrone_ctx_run_linear_fn(self.ctx, monodrone_ctx_get_cursor_sync_index) } {
            self.selection = Selection::from_lean(self.ctx);
        }

        self.playback_speed = get_playback_speed(self.ctx);
    }


    pub fn track(&self) -> &UITrack {
        &self.track
    }

    pub fn selection(&self) -> &Selection {
        &self.selection
    }

    pub fn playback_speed(&self) -> f64 {
        self.playback_speed
    }

    pub fn file_path(&self) -> &PathBuf {
        &self.file_path
    }

    pub fn set_playback_speed(&mut self, value : f64) {
        unsafe {
            self.ctx = set_playback_speed(self.ctx, value);
        }
    }

    pub fn to_json_string(&self) -> String {
        ctx_to_json_string(self.ctx)
    }

    pub fn get_midi_export_file_path(&self) -> PathBuf {
        let mut out = self.file_path.clone();
        out.pop();
        out.push(out.as_path().file_stem().unwrap().to_string_lossy().to_string() + ".mid");
        out
    }

    pub fn set_pitch (&mut self, pitch : PitchName) {
        self.run_ctx_fn(|ctx| set_pitch(ctx, pitch))
    }

    pub fn cursor_move_left_one (&mut self) {
        self.run_ctx_fn(|ctx| cursor_move_left_one(ctx))
    }

    pub fn cursor_move_right_one (&mut self) {
        self.run_ctx_fn(|ctx| cursor_move_right_one(ctx))
    }

    pub fn cursor_move_down_one (&mut self) {
        self.run_ctx_fn(|ctx| cursor_move_down_one(ctx))
    }

    pub fn cursor_move_up_one (&mut self) {
        self.run_ctx_fn(|ctx| cursor_move_up_one(ctx))
    }

    pub fn toggle_sharp (&mut self) {
        self.run_ctx_fn(|ctx| toggle_sharp(ctx))
    }

    pub fn toggle_flat (&mut self) {
        self.run_ctx_fn(|ctx| toggle_flat(ctx))
    }

    pub fn newline (&mut self) {
        self.run_ctx_fn(|ctx| newline(ctx))
    }

    pub fn delete_line (&mut self) {
        self.run_ctx_fn(|ctx| delete_line(ctx))
    }

    pub fn delete_note (&mut self) {
        self.run_ctx_fn(|ctx| delete_note(ctx))
    }

    pub fn lower_octave (&mut self) {
        self.run_ctx_fn(|ctx| lower_octave(ctx))
    }

    pub fn raise_octave (&mut self) {
        self.run_ctx_fn(|ctx| raise_octave(ctx))
    }

    pub fn increase_nsteps (&mut self) {
        self.run_ctx_fn(|ctx| increase_nsteps(ctx))
    }

    pub fn decrease_nsteps (&mut self) {
        self.run_ctx_fn(|ctx| decrease_nsteps(ctx))
    }

    pub fn undo_action (&mut self) {
        self.run_ctx_fn(|ctx| undo_action(ctx))
    }

    pub fn redo_action (&mut self) {
        self.run_ctx_fn(|ctx| redo_action(ctx))
    }

}
