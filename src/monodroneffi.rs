
use crate::leanffi::{self, lean_inc_ref_cold};

extern {
    fn monodrone_new_context(val : *mut i8) -> *mut i8;
    pub fn initialize_Monodrone(builtin : u8, world : *mut i8) -> i8;

    pub fn monodrone_track_length(ctx : *mut i8) -> u64;
    pub fn monodrone_track_get_note(ctx : *mut i8, ix : u64) -> *mut i8;
    pub fn monodrone_note_get_pitch(n : *mut i8) -> u64;
    pub fn monodrone_note_get_start(n : *mut i8) -> u64;
    pub fn monodrone_note_get_nsteps(n : *mut i8) -> u64;
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
    pub notes: Vec<Note>,
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
