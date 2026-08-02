#![allow(dead_code, unused_variables, unused_unsafe, internal_features)]
#![feature(core_intrinsics)]

use std::fmt::Debug;

pub async fn wait(a: u32) -> u32 {
    let b = inner(a).await;
    b + 1
}

async fn inner(a: u32) -> u32 {
    a * 2
}

pub fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}

pub struct Holder<'a> {
    pub inner: &'a [u8],
}

impl<'a> Holder<'a> {
    pub fn first(&self) -> Option<&'a u8> {
        self.inner.first()
    }
}

pub trait Store {
    type Item: Debug;
    fn get(&self) -> Self::Item;
}

pub fn fetch<S>(s: &S) -> S::Item
where
    S: Store,
    S::Item: Clone,
{
    s.get()
}

pub fn outlives<'a, 'b: 'a, T: 'a>(x: &'a T, y: &'b T) -> &'a T {
    x
}

pub fn scalars(c: char, f: f32, x: i128, y: u128) -> u128 {
    let a = c as u32;
    let b = f as f64;
    let d = x as u128;
    a as u128 + b as u128 + d + y
}

pub fn raw_ops(v: &mut [u32]) -> usize {
    let p: *const [u32] = &raw const *v;
    let q: *mut u32 = &raw mut v[0];
    unsafe {
        *q = 1;
    }
    p.len()
}

pub unsafe fn casts(x: u64) -> *const u8 {
    let a: f64 = std::mem::transmute(x);
    let b = (a as u64 + x) as *const ();
    let c: *const u8 = b.cast();
    c
}

pub unsafe fn intrinsics(src: *const u8, dst: *mut u8, n: usize, flag: bool) {
    std::intrinsics::assume(flag);
    std::ptr::copy_nonoverlapping(src, dst, n);
}

#[cfg(target_arch = "x86_64")]
pub unsafe fn asm_add(a: u64) -> u64 {
    let out: u64;
    std::arch::asm!("mov {out}, {inp}", out = out(reg) out, inp = in(reg) a);
    out
}

pub fn arrays() -> [u32; 4] {
    let a = [1u32, 2, 3, 4];
    let b = [0u32; 4];
    [a[0] + b[0], a[1], a[2], a[3]]
}

pub union Bits {
    pub i: u32,
    pub f: f32,
}

pub fn union_read(b: Bits) -> u32 {
    unsafe { b.i }
}

pub fn nested(n: u32) -> impl Fn(u32) -> u32 {
    let f = move |x: u32| x + n;
    move |y: u32| f(y) * 2
}

pub fn diverge() -> ! {
    panic!("gone")
}

pub fn count(n: u64) -> u64 {
    if n == 0 { 0 } else { count(n - 1) + 1 }
}
