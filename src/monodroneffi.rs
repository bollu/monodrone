
use crate::leanffi::{self, lean_inc_ref_cold};

extern {
    fn monodrone_new_context(val : *mut i8) -> *mut i8;
    pub fn initialize_Monodrone(builtin : u8, world : *mut i8) -> i8;

    pub fn monodrone_track_length(ctx : *mut i8) -> u64;
    pub fn monodrone_track_get_note(ctx : *mut i8, ix : u64) -> *mut i8;
    pub fn monodrone_note_get_pitch(n : *mut i8) -> u64;
    pub fn monodrone_note_get_start(n : *mut i8) -> u64;
    pub fn monodrone_note_get_nsteps(n : *mut i8) -> u64;
    // https://www.sublimetext.com/docs/api_reference.html#sublime.Region
    pub fn monodrone_ctx_cursor_a(ctx : *mut i8) -> u64;
    pub fn monodrone_ctx_cursor_b(ctx : *mut i8) -> u64;
}
pub fn initialize() -> () {
    unsafe { initialize_Monodrone(1, leanffi::lean_box(0)) };
}
pub fn new_context() -> *mut i8 {
    unsafe { monodrone_new_context(leanffi::lean_box(0)) }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Note {
    pub pitch: u64,
    pub start: u64,
    pub nsteps: u64,
}


#[derive(Debug, Clone, PartialEq)]
pub struct Track {
    pub notes: Vec<Note>, // sorted by start
}

impl Track {
    pub fn new() -> Track {
        Track { notes: Vec::new() }
    }
    
}

#[derive(Debug, Clone, PartialEq)]
pub struct TrackBuilder {
    notes: Vec<Note>,
    time : u64,
}
impl TrackBuilder {
    pub fn new() -> TrackBuilder {
        TrackBuilder { notes: Vec::new(), time: 0 }
    }

    /// Add a note to the track that is held for `nsteps` steps.
    pub fn note_held(&mut self, pitch: u64, nsteps: u64) -> &mut Self {
        self.notes.push(Note { pitch, start: self.time, nsteps });
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

    pub fn build(&self) -> Track {
        Track { notes: self.notes.clone() }
    }
}


impl From<TrackBuilder> for Track {
    fn from(builder: TrackBuilder) -> Self {
        Track { notes: builder.notes }
    }
}

pub fn get_cursor_a (ctx : *mut i8) -> u64 {
    unsafe {
        lean_inc_ref_cold(ctx);
        monodrone_ctx_cursor_a(ctx)
    }
}

pub fn get_cursor_b (ctx : *mut i8) -> u64 {
    unsafe {
        lean_inc_ref_cold(ctx);
        monodrone_ctx_cursor_b(ctx)
    }
}


pub fn get_track (ctx : *mut i8) -> Track {
    let len: u64 = unsafe {
        lean_inc_ref_cold(ctx);
        monodrone_track_length(ctx)
    };
    let mut notes: Vec<Note> = Vec::new();
    for i in 0..len {
        unsafe { lean_inc_ref_cold(ctx); }
        let note = unsafe { monodrone_track_get_note(ctx, i) };
        unsafe { lean_inc_ref_cold(note) };
        let pitch = unsafe { monodrone_note_get_pitch(note) };
        unsafe { lean_inc_ref_cold(note) };
        let start = unsafe { monodrone_note_get_start(note) };
        unsafe { lean_inc_ref_cold(note) };
        let nsteps = unsafe { monodrone_note_get_nsteps(note) };
        notes.push(Note { pitch, start, nsteps });
    }

    Track { notes }
}
