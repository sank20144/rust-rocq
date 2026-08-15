pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

pub fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

pub fn collatz_steps(mut n: u64) -> u64 {
    let mut steps = 0;
    while n != 1 {
        if n % 2 == 0 {
            n = n / 2;
        } else {
            n = 3 * n + 1;
        }
        steps += 1;
    }
    steps
}

pub fn spin(n: u64) -> u64 {
    let mut i = n;
    loop {
        if i == 0 {
            i = 1;
        } else {
            i = 0;
        }
    }
}

pub fn id<T>(x: T) -> T {
    x
}
