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

extern {
    // see https://leanprover.github.io/lean4/doc/dev/ffi.html#initialization
    // extern void lean_initialize_runtime_module();
    pub fn lean_initialize_runtime_module ();

    // extern void lean_io_mark_end_initialization();
    pub fn lean_io_mark_end_initialization ();

    // extern "C" LEAN_EXPORT void lean_inc_ref_cold(lean_object * o) {
    pub fn lean_inc_ref_cold (ptr: *mut boxed);
}

impl boxed {
    pub fn inc(ptr : *mut boxed) -> *mut Self{
        unsafe { lean_inc_ref_cold(ptr) }
        ptr
    }
}