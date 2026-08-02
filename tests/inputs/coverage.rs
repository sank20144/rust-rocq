#![allow(dead_code, unused_variables, unused_unsafe)]

use std::fmt::Debug;

pub enum Shape {
    Point,
    Circle(f64),
    Rect { w: u32, h: u32 },
}

pub fn area(s: &Shape) -> u64 {
    match s {
        Shape::Point => 0,
        Shape::Circle(r) => (*r as u64) * 3,
        Shape::Rect { w, h } => (*w as u64) * (*h as u64),
    }
}

pub fn make(n: u32) -> Shape {
    if n == 0 {
        Shape::Point
    } else {
        Shape::Rect { w: n, h: n }
    }
}

pub fn slices(v: &[u8]) -> u8 {
    let arr = [7u8; 16];
    let mut t = arr[3];
    if let [first, .., last] = v {
        t = t.wrapping_add(*first).wrapping_add(*last);
    }
    if let [_, rest @ ..] = v {
        t = t.wrapping_add(rest.len() as u8);
    }
    t
}

pub fn drops(c: bool, s: String) -> usize {
    let t = String::from("other");
    if c {
        drop(s);
        t.len()
    } else {
        s.len() + t.len()
    }
}

pub unsafe fn raw(p: *const u32, q: *mut u32) -> usize {
    let a = *p;
    *q = a.wrapping_add(1);
    let addr = p as usize;
    let back = addr as *const u32;
    let f = a as f64;
    let g = f as i8;
    addr + (g as usize) + (back as usize)
}

pub fn borrows(v: &mut Vec<u32>) {
    v.push(v.len() as u32);
    let first = &mut v[0];
    *first += 1;
}

pub fn largest<T: PartialOrd + Copy>(items: &[T]) -> Option<T> {
    let mut best: Option<T> = None;
    for it in items {
        best = match best {
            None => Some(*it),
            Some(b) if *it > b => Some(*it),
            keep => keep,
        };
    }
    best
}

pub fn sum_fixed<const N: usize>(xs: [u32; N]) -> u32 {
    let mut t = 0;
    let mut i = 0;
    while i < N {
        t += xs[i];
        i += 1;
    }
    t
}

pub trait Speak {
    fn speak(&self) -> u32;
}

pub struct Dog;
impl Speak for Dog {
    fn speak(&self) -> u32 {
        1
    }
}

pub fn dynamic(x: &dyn Speak) -> u32 {
    x.speak()
}

pub fn boxed() -> Box<dyn Speak> {
    Box::new(Dog)
}

pub fn closures(n: u32) -> u32 {
    let add = |x: u32| x + n;
    let owned = String::from("hi");
    let consume = move || owned.len() as u32;
    add(1) + consume()
}

pub fn fnptr() -> u32 {
    let f: fn(&Dog) -> u32 = Dog::speak;
    f(&Dog)
}

pub fn checks(a: u32, b: u32, v: &[u32]) -> u32 {
    let d = a / b;
    let m = a % b;
    let x = v[a as usize];
    let n = -(a as i32);
    d + m + x + (n as u32)
}

pub static GLOBAL: u32 = 9;

thread_local! {
    pub static LOCAL: u32 = 3;
}

pub fn read_static() -> u32 {
    GLOBAL + LOCAL.with(|v| *v)
}

pub fn fallible(x: Option<u32>) -> Option<u32> {
    let y = x?;
    Some(y + 1)
}

pub fn describe<T>(items: Vec<T>) -> usize
where
    T: Debug + Clone,
{
    items.len()
}

pub struct Pair {
    pub a: u32,
    pub b: (u8, u16),
}

pub fn fields(p: Pair) -> u32 {
    p.a + p.b.0 as u32 + p.b.1 as u32
}

pub fn bits(mut x: u64) -> u64 {
    loop {
        x = (x << 1) | (x >> 63);
        x ^= 0xff;
        x &= !0x0f;
        if x == 0 {
            break x | 1;
        }
        if x > 1 << 40 {
            break x;
        }
    }
}
