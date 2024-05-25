use libc::uint8_t;

use crate::leanffi;

#[repr(C)]
pub struct MonodroneContext {
    _data: [u8; 0],
    _marker:
        core::marker::PhantomData<(*mut u8, core::marker::PhantomPinned)>,
}

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

    pub fn monodrone_track_length(ctx : *mut MonodroneContext) -> u32;
    pub fn monodrone_track_get_note(ctx : *mut MonodroneContext, ix : u32) -> *mut leanffi::boxed;
    pub fn monodrone_note_get_pitch(n : *mut leanffi::boxed) -> u32;
    pub fn monodrone_note_get_start(n : *mut leanffi::boxed) -> u32;
    pub fn monodrone_note_get_nsteps(n : *mut leanffi::boxed) -> u32;
}
pub fn initialize() -> () {
    unsafe { initialize_Monodrone(1, leanffi::lean_box(0)) };
}
pub fn new_context() -> *mut MonodroneContext {
    unsafe { monodrone_new_context(leanffi::lean_box(0)) }
}

pub struct Note {
    pitch: u32,
    start: u32,
    nsteps: u32,
}

pub struct Track {
    notes: Vec<Note>,
}

pub fn get_track (ctx : *mut MonodroneContext) -> Track {
    let mut notes = Vec::new();
    let len = unsafe { monodrone_track_length(ctx) };
    // for i in 0..len {
    //     let note = unsafe { monodrone_track_get_note(ctx, i) };
    //     let pitch = unsafe { monodrone_note_get_pitch(note) };
    //     let start = unsafe { monodrone_note_get_start(note) };
    //     let nsteps = unsafe { monodrone_note_get_nsteps(note) };
    //     notes.push(Note { pitch, start, nsteps });
    // }
    Track { notes }
}