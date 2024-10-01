
use std::{collections::HashMap, path::PathBuf};
use lean_sys::{lean_box, lean_dec_ref, lean_inc_ref, lean_io_result_get_error, lean_object, lean_unbox_float};
use serde::{Serialize, Deserialize};


use tracing::{event, Level};

use crate::{track_get_note_events_at_time};

#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub struct PlayerNote {
    pub y : u64,
    pub start: u64,
    pub nsteps: u64,

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


impl PlayerNote {
    pub fn pitch(&self) -> u64 {
        ui_pitch_to_midi_pitch(self.pitch_name, self.accidental, self.octave)
    }

    pub fn to_str (&self) -> String {
        format!("{}{}", self.pitch_name.to_str(), self.accidental.to_str())
    }
}


#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
pub struct PlayerTrack {
    pub notes: Vec<PlayerNote>, // sorted by start
    pub hitbox : HashMap<(u64, u64), usize>, // maps (x, y) to index in notes.
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

    pub fn get_note_from_coord (&self, x : u64, y : u64) -> Option<&PlayerNote> {
        match self.hitbox.get(&(x, y)) {
            Some(ix) => Some(&self.notes[*ix]),
            None => None,
        }
    }

    pub fn get_last_instant (&self) -> u64 {
        self.notes.iter().map(|note| note.y + note.nsteps).max().unwrap_or(0)
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
}

const NTRACKS : u32 = 4;
const TRACK_LENGTH : u32 = 100;


#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Selection {
    pub cursor : egui::Pos2,
    pub x : u32,
    pub y : u32,
}


impl Selection {
    fn new() -> Selection {
        Selection {
            cursor: egui::Pos2::new(0.0, 0.0),
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
#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct Context {
    pub file_path : PathBuf,
    pub track : PlayerTrack,
    pub selection : Selection,
    pub playback_speed : f64,
    pub track_name : String,
    pub artist_name : String,
    pub time_signature : (u8, u8),
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
        }

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
        for note in self.track.notes.iter() {
            let end = note.start + note.nsteps;
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
        }
    }
}
