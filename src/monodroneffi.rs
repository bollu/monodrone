
use crate::leanffi::{self, lean_inc_ref_cold};

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

    fn monodrone_new_context(val : *mut i8) -> *mut i8;
    pub fn initialize_Monodrone(builtin : u8, world : *mut i8) -> i8;

    pub fn monodrone_track_length(ctx : *mut i8) -> u64;
    pub fn monodrone_track_get_note(ctx : *mut i8, ix : u64) -> *mut i8;
    pub fn monodrone_note_get_pitch(n : *mut i8) -> u64;
    pub fn monodrone_note_get_start(n : *mut i8) -> u64;
    pub fn monodrone_note_get_nsteps(n : *mut i8) -> u64;
    // @[export monodrone_dummy]
    // def throwContext (x : RawContext) : UInt64 := 0
    pub fn monodrone_dummy(ctx : *mut i8) -> u64;

}
pub fn initialize() -> () {
    unsafe { initialize_Monodrone(1, leanffi::lean_box(0)) };
}
pub fn new_context() -> *mut i8 {
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


pub fn get_track (ctx : *mut i8) -> Track {
    println!("get_track: {:p}", ctx);
    println!("lean_inc_ref_cold");
    println!("calling monodrone_track_length");
    let len: u64 = unsafe {
        lean_inc_ref_cold(ctx);
        monodrone_track_length(ctx)
    };
    println!("len: {}", len);

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
