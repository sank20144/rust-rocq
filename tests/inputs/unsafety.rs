#![allow(dead_code, unused_unsafe)]

pub unsafe fn deref(p: *const u32) -> u32 {
    *p
}

pub fn call_it(p: *const u32) -> u32 {
    unsafe { deref(p) }
}

pub fn take_addr(x: &mut u32) -> *mut u32 {
    x as *mut u32
}

pub fn write_through(x: &mut u32, v: u32) {
    let p = x as *mut u32;
    unsafe {
        *p = v;
    }
}

pub union Bits {
    pub i: u32,
    pub f: f32,
}

pub fn as_float(b: Bits) -> f32 {
    unsafe { b.f }
}

pub static mut COUNT: u32 = 0;

pub fn bump() -> u32 {
    unsafe {
        COUNT += 1;
        COUNT
    }
}

pub fn as_ptr_fn() -> unsafe fn(*const u32) -> u32 {
    deref
}

pub fn safe_add(a: u32, b: u32) -> u32 {
    a + b
}

pub fn as_safe_ptr_fn() -> fn(u32, u32) -> u32 {
    safe_add
}

pub fn as_unsafe_ptr_fn() -> unsafe fn(u32, u32) -> u32 {
    safe_add
}

pub fn widen(f: fn(u32, u32) -> u32) -> unsafe fn(u32, u32) -> u32 {
    f
}

pub fn offset(p: *const u32, n: usize) -> *const u32 {
    unsafe { p.add(n) }
}
