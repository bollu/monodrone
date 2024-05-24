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
}

pub fn new_context() -> *mut MonodroneContext {
    unsafe { monodrone_new_context(leanffi::lean_box(0)) }
}
