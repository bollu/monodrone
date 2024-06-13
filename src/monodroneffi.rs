
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
    pub fn monodrone_ctx_move_down_one(ctx : *mut i8) -> *mut i8;
    pub fn monodrone_ctx_move_up_one(ctx : *mut i8) -> *mut i8;
    pub fn monodrone_ctx_add_note_c(ctx : *mut i8) -> *mut i8;
    pub fn monodrone_ctx_lower_semitone(ctx : *mut i8) -> *mut i8;
    pub fn monodrone_ctx_raise_semitone(ctx : *mut i8) -> *mut i8;
    
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


/// Run a function that is linear in the monodrone ctx, so we bump the ref count once and then call the function.
pub fn monodrone_ctx_run_linear_fn<T> (ctx : *mut i8, f : unsafe extern "C" fn(*mut i8) -> T) -> T {
    unsafe {
        lean_inc_ref_cold(ctx);
        f(ctx)
    }
}

pub fn get_cursor_a (ctx : *mut i8) -> u64 {
    monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_cursor_a)
}

pub fn get_cursor_b (ctx : *mut i8) -> u64 {
    monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_cursor_b)
}


pub fn get_track (ctx : *mut i8) -> Track {
    let len: u64 = unsafe {
        lean_inc_ref_cold(ctx);
        monodrone_track_length(ctx)
    };
    let mut notes: Vec<Note> = Vec::new();
    for i in 0..len {
        unsafe { 
            lean_inc_ref_cold(ctx); 
            let note = monodrone_track_get_note(ctx, i);
            lean_inc_ref_cold(note);
            let pitch = monodrone_note_get_pitch(note);
            lean_inc_ref_cold(note);
            let start = monodrone_note_get_start(note);
            lean_inc_ref_cold(note);
            let nsteps = monodrone_note_get_nsteps(note);
            notes.push(Note { pitch, start, nsteps });
        }
    }

    Track { notes }
}

/// TODO: ask Theo how to automatically do this.
pub fn move_down_one (ctx : *mut i8) -> *mut i8 {
    monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_move_down_one)
}

pub fn move_up_one (ctx : *mut i8) -> *mut i8 {
    monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_move_up_one)
}

pub fn add_note_c (ctx : *mut i8) -> *mut i8 {
    monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_add_note_c)
}

pub fn lower_semitone (ctx : *mut i8) -> *mut i8 {
    monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_lower_semitone)
}

pub fn raise_semitone (ctx : *mut i8) -> *mut i8 {
    monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_raise_semitone)
}
