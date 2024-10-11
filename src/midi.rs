use tracing::event;
use midi;
use std::{fs::File, sync::Arc};
use tinyaudio::{run_output_device, OutputDeviceParameters};
use std::sync::Mutex;
use std::thread::{current, sleep};
use std::collections::HashMap;
use rustysynth::{SoundFont, Synthesizer, SynthesizerSettings};
use tinyaudio::prelude::*;
use tracing::{Level};

use crate::datastructures::*;


#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NoteEvent {
    NoteOn { pitch: u8, instant: u64 },
    NoteOff { pitch: u8, instant: u64 },
}

impl NoteEvent {
    pub fn instant(&self) -> u64 {
        match self {
            NoteEvent::NoteOn { instant, .. } => *instant,
            NoteEvent::NoteOff { instant, .. } => *instant,
        }
    }

    pub fn pitch(&self) -> u8 {
        match self {
            NoteEvent::NoteOn { pitch, .. } => *pitch,
            NoteEvent::NoteOff { pitch, .. } => *pitch,
        }
    }

    pub fn to_midi_message(self) -> midly::MidiMessage {
        match self {
            NoteEvent::NoteOn { pitch, .. } =>  {
                midly::MidiMessage::NoteOn {
                    key: midly::num::u7::from_int_lossy(pitch),
                    vel: midly::num::u7::from_int_lossy(100),
                }
            },
            NoteEvent::NoteOff { pitch, .. } =>  {
                midly::MidiMessage::NoteOff {
                    key: midly::num::u7::from_int_lossy(pitch),
                    vel: midly::num::u7::from_int_lossy(100),
                }
            }
        }
    }
}

// order note events by instant
impl PartialOrd for NoteEvent {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for NoteEvent {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // compare tuple of (instant, pitch)
        (self.instant(), self.pitch()).cmp(&(other.instant(), other.pitch()))
    }
}

/// Get the note events at a given time instant.
// TODO: make this a method of the track.
pub fn track_get_note_events_at_time(
    track: &PlayerTrack,
    instant: u64,
) -> Vec<NoteEvent> {
    let mut note_events = Vec::new();
    let mut ix2pitches: HashMap<u64, Vec<i64>> = HashMap::new();

    for note in track.notes.iter() {
        ix2pitches
            .entry(note.start)
            .or_default()
            .push(note.pitch());
    }
    // only emit a note off if there is no same note in the next time step.
    // Otherwise, we hear a jarring of a note being "stacattod" where we
    // turn it off and on in the same instant.
    for note in track.notes.iter() {
        if (note.start + note.nsteps as u64) == instant {
            let off_event = NoteEvent::NoteOff {
                pitch: note.pitch() as u8,
                instant,
            };
            match ix2pitches.get(&(note.start + note.nsteps as u64)) {
                Some(next_notes) => {
                    if !next_notes.contains(&note.pitch()) {
                        note_events.push(off_event);
                    }
                }
                None => {
                    note_events.push(off_event);
                }
            }
        }
        if note.start == instant {
            note_events.push(NoteEvent::NoteOn {
                pitch: note.pitch() as u8,
                instant,
            });
        }
    }
    note_events
}

pub struct MidiSequencer {
    pub synthesizer: Synthesizer,
    pub track: PlayerTrack,
    pub playing: bool,
    pub start_instant: u64,
    pub end_instant: u64,
    pub cur_instant: f32,           // current instant of time, as we last heard.
    pub last_rendered_instant: u64, // instant of time we last rendered.
    pub looping: bool,
    pub num_instants_wait_before_loop: u64,
    pub instant_delta: f32, // how many instants we increment at each tick. each tick is called at 1/10 of a second.
}

impl MidiSequencer {
    /// Initializes a new instance of the sequencer.
    ///
    /// # Arguments
    ///
    /// * `synthesizer` - The synthesizer to be handled by the sequencer.
    /// * `track` - The track to be played for this sequencer.
    pub fn new(synthesizer: Synthesizer) -> Self {
        Self {
            synthesizer,
            track: PlayerTrack::new(),
            playing: false,
            cur_instant: 0.0,
            start_instant: 0,
            last_rendered_instant: 0,
            looping: false,
            end_instant: 0,
            num_instants_wait_before_loop: 0,
            instant_delta: 0.5,
        }
    }

    pub fn set_track(&mut self, track: PlayerTrack) {
        assert!(!self.playing); // we cannot change the track while playing.
        self.track = track;
    }

    /// Stops playing. Keep current location.
    pub fn pause(&mut self) {
        self.synthesizer.reset();
        self.playing = false;
        //self.cur_instant = 0.0;
        //self.last_rendered_instant = 0;
    }

    pub fn play(&mut self) {
        self.playing = true;
    }

    pub fn start_afresh(&mut self, start_instant: u64, end_instant: u64, looping: bool) {
        self.playing = true;
        self.cur_instant = start_instant as f32;
        self.start_instant = start_instant;
        self.end_instant = end_instant;
        self.looping = looping;
        self.last_rendered_instant = start_instant;
    }

    pub fn process_and_render(&mut self, left: &mut [f32], right: &mut [f32]) {
        let new_instant = self.cur_instant + self.instant_delta;
        // event!(
        //     Level::INFO,
        //     "process_and_render cur({}) -> new({}) |
        //      last rendered({}) | end({}) is_playing({}) | looping ({})",
        //     self.cur_instant,
        //     new_instant,
        //     self.last_rendered_instant,
        //     self.end_instant,
        //     self.playing,
        //     self.looping
        // );

        self.synthesizer.render(&mut left[0..], &mut right[0..]);

        if !self.playing {
            return;
        }

        if self.cur_instant >= self.end_instant as f32 {
            if !self.looping {
                self.playing = false;
                return;
            }
            let NUM_INSTANTS_WAIT_BEFORE_LOOP = 2;
            self.num_instants_wait_before_loop += 1;
            if self.num_instants_wait_before_loop >= NUM_INSTANTS_WAIT_BEFORE_LOOP {
                self.cur_instant = self.start_instant as f32;
                self.last_rendered_instant = self.start_instant;
                self.playing = true;
                self.num_instants_wait_before_loop = 0;
            }
        } else {
            assert!(self.last_rendered_instant <= self.cur_instant as u64);
            assert!(self.cur_instant <= new_instant);
            self.cur_instant = new_instant;

            assert!(left.len() == right.len());
            assert!(left.len() >= self.synthesizer.get_block_size()); // we have enough space to render at least one block.

            while new_instant - self.last_rendered_instant as f32 >= 1.0 {
                let note_events =
                    track_get_note_events_at_time(&self.track, self.last_rendered_instant);
                for note_event in note_events.iter() {
                    event!(Level::INFO, "note_event: {:?}", note_event);
                    match note_event {
                        NoteEvent::NoteOff { pitch, .. } => {
                            self.synthesizer.note_off(0, *pitch as i32);
                        }
                        NoteEvent::NoteOn { pitch, .. } => {
                            self.synthesizer.note_on(0, *pitch as i32, 100);
                        }
                    }
                }
                self.last_rendered_instant += 1; // we have rendered this instant.
            }
        }
    }
}


/// Module that performs the IO for the midi sequencer inside it.
/// Furthermore, it allows the track for the MIDI sequencer to be changed,
/// as well as changing playback settings (e.g. part of sequencer to loop).
pub struct MidiSequencerIO {
    pub sequencer: Arc<Mutex<MidiSequencer>>,
    pub params: OutputDeviceParameters,
    pub device: Box<dyn BaseAudioOutputDevice>,
}


impl MidiSequencerIO {
    pub fn new(sequencer: MidiSequencer, params: OutputDeviceParameters) -> Self {
        let sequencer = Arc::new(Mutex::new(sequencer));
        // The output buffer (3 seconds).
        let mut left: Vec<f32> = vec![0_f32; params.channel_sample_count];
        let mut right: Vec<f32> = vec![0_f32; params.channel_sample_count];
        let _t = 0;
        let device: Box<dyn BaseAudioOutputDevice> = run_output_device(params, {
            let sequencer = sequencer.clone();
            move |data| {
                // event!(Level::INFO, "running audio device");
                sequencer
                    .lock()
                    .as_mut()
                    .unwrap()
                    .process_and_render(&mut left[..], &mut right[..]);

                for i in 0..data.len() {
                    if i % 2 == 0 {
                        data[i] = left[i / 2];
                    } else {
                        data[i] = right[i / 2];
                    }
                }
            }
        })
        .unwrap();
        MidiSequencerIO {
            sequencer: sequencer.clone(),
            params,
            device,
        }
    }

    pub fn is_playing(&self) -> bool {
        self.sequencer.lock().as_ref().unwrap().playing
    }

    pub fn stop(&mut self) {
        self.sequencer.lock().as_mut().unwrap().pause();
    }

    pub fn play(&mut self) {
        self.sequencer.lock().as_mut().unwrap().play();
    }

    pub fn set_playback_speed(&mut self, instant_delta: f32) {
        let mut seq_changer = self.sequencer.lock().unwrap();
        seq_changer.instant_delta = instant_delta;
    }

    pub fn restart(&mut self, start_instant: u64, end_instant: u64, looping: bool) {
        event!(Level::INFO, "### restarting ###");
        let mut seq_changer = self.sequencer.lock().unwrap();

        seq_changer.looping = looping;
        seq_changer.start_instant = start_instant;
        seq_changer.end_instant = end_instant;
        seq_changer.start_afresh(start_instant, end_instant, looping);
    }

    // TODO: figure out how to give this guy a reference to the track.
    pub fn set_track(&mut self, track: PlayerTrack) {
        self.sequencer.lock().as_mut().unwrap().track = track;
    }
}
