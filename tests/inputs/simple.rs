pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

pub fn choose(c: bool, x: &u32, y: &u32) -> u32 {
    if c { *x } else { *y }
}

pub fn sum(v: &[u32]) -> u32 {
    let mut t = 0u32;
    let mut i = 0usize;
    while i < v.len() {
        t += v[i];
        i += 1;
    }
    t
}
