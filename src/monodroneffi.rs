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

    fn monodrone_new_context(val : *mut leanffi::boxed) -> *mut MonodroneContext;
    pub fn initialize_Monodrone(builtin : u8, world : *mut leanffi::boxed) -> leanffi::boxed;
    pub fn monodrone_context_num_pitches(ctx : *mut MonodroneContext) -> i32;

}
pub fn initialize() -> () {
    unsafe { initialize_Monodrone(1, leanffi::lean_box(0)) };
}
pub fn new_context() -> *mut MonodroneContext {
    unsafe { monodrone_new_context(leanffi::lean_box(0)) }
}
