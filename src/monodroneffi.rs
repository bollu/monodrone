use libc::uint8_t;

use crate::leanffi::{self, boxed};


type MonodroneContext = leanffi::boxed;

#[link(name = "Monodrone")]
extern {
    // @[export monodrone_new_context]
    // def newContext (_ : Unit) : LawfulRawContext := LawfulRawContext.empty
    
    // @[export monodrone_track_length]
    // def trackLength (ctx : RawContext) : Nat := ctx.tracks.notes.length
    
    // @[export monodrone_track_get_note]
    // def trackGetNote (ctx : RawContext) (ix : Nat) : Note :=
    //   ctx.tracks.notes.get! ix
    
    // @[export monodrone_note_get_pitch]
    // def noteGetPitch (n : Note) : Pitch := n.pitch
    
    // @[export monodrone_note_get_start]
    // def noteGetStart (n : Note) : Nat := n.start
    
    // @[export monodrone_note_get_nsteps]
    // def noteGetNsteps (n : Note) : Nat := n.nsteps
    
    fn monodrone_new_context(val : *mut leanffi::boxed) -> *mut MonodroneContext;
    pub fn initialize_Monodrone(builtin : u8, world : *mut leanffi::boxed) -> leanffi::boxed;

    pub fn monodrone_track_length(ctx : *mut MonodroneContext) -> u64;
    pub fn monodrone_track_get_note(ctx : *mut MonodroneContext, ix : u64) -> *mut leanffi::boxed;
    pub fn monodrone_note_get_pitch(n : *mut leanffi::boxed) -> u64;
    pub fn monodrone_note_get_start(n : *mut leanffi::boxed) -> u64;
    pub fn monodrone_note_get_nsteps(n : *mut leanffi::boxed) -> u64;
}
pub fn initialize() -> () {
    unsafe { initialize_Monodrone(1, leanffi::lean_box(0)) };
}
pub fn new_context() -> *mut MonodroneContext {
    unsafe { monodrone_new_context(leanffi::lean_box(0)) }
}

pub struct Note {
    pitch: u64,
    start: u64,
    nsteps: u64,
}

pub struct Track {
    notes: Vec<Note>,
}

pub fn get_track (ctx : *mut MonodroneContext) -> Track {
    boxed::inc(ctx);
    let len: u64 = unsafe { monodrone_track_length(ctx) };
    // println!("len: {}", len);

    let mut notes: Vec<Note> = Vec::new();
    // for i in 0..len {
    //     boxed::inc(ctx);
    //     let note = unsafe { monodrone_track_get_note(ctx, i) };
    //     boxed::inc(note);

    //     // this is a bug in Lean's FFI.
    //     let pitch = unsafe { monodrone_note_get_pitch(note) };
    //     // boxed::inc(ctx);
    //     // let start = unsafe { monodrone_note_get_start(note) };
    //     // boxed::inc(ctx);
    //     // let nsteps = unsafe { monodrone_note_get_nsteps(note) };
    //     // notes.push(Note { pitch, start, nsteps });
    // }
    Track { notes }
}