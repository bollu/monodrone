// static inline lean_object * lean_box(size_t n) { return (lean_object*)(((size_t)(n) << 1) | 1); }
pub fn lean_box (val : usize) -> *mut i8 {
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
    pub fn lean_inc_ref_cold (ptr: *mut i8);
}
