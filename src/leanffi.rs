#[repr(C)]
pub struct boxed {
    _data: [u8; 0],
    _marker:
        core::marker::PhantomData<(*mut u8, core::marker::PhantomPinned)>,
}

// static inline lean_object * lean_box(size_t n) { return (lean_object*)(((size_t)(n) << 1) | 1); }
pub fn lean_box (val : usize) -> *mut boxed {
    let out : usize = (val << 1) | 1;
    unsafe {
        std::mem::transmute(out)
    }
}