#[repr(C)]
pub struct MonodroneContext {
    _data: [u8; 0],
    _marker:
        core::marker::PhantomData<(*mut u8, core::marker::PhantomPinned)>,
}

#[link(name = "Monodrone")]
extern {
    pub fn new_context() -> *mut MonodroneContext;
}
