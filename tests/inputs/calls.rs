pub fn double(x: u32) -> u32 {
    x * 2
}

pub fn quadruple(x: u32) -> u32 {
    double(double(x))
}

pub fn factorial(n: u16) -> u16 {
    if n == 0 { 1 } else { n * factorial(n - 1) }
}

pub fn is_even(n: u32) -> bool {
    if n == 0 { true } else { is_odd(n - 1) }
}

pub fn is_odd(n: u32) -> bool {
    if n == 0 { false } else { is_even(n - 1) }
}

pub fn bump(x: &mut u32) {
    *x += 1;
}

pub fn bump_twice(x: u32) -> u32 {
    let mut y = x;
    bump(&mut y);
    bump(&mut y);
    y
}

pub fn succ(x: u8) -> u8 {
    x + 1
}

pub fn succ_of_succ(x: u8) -> u8 {
    succ(succ(x))
}

pub fn id<T>(x: T) -> T {
    x
}

pub fn pick<T: Copy>(first: bool, a: T, b: T) -> T {
    if first { a } else { b }
}

pub fn through_id(x: u32) -> u32 {
    id(x)
}

pub fn pick_second(a: bool, b: bool) -> bool {
    pick(false, a, b)
}

pub struct Pair {
    pub a: u32,
    pub b: u32,
}

pub fn make_pair(a: u32, b: u32) -> Pair {
    Pair { a, b }
}

pub fn sum_pair(p: Pair) -> u32 {
    p.a + p.b
}

pub fn pair_round_trip(a: u32, b: u32) -> u32 {
    sum_pair(make_pair(a, b))
}

pub fn swap_in_place(p: &mut Pair) {
    let t = p.a;
    p.a = p.b;
    p.b = t;
}

pub fn swapped_difference(a: u32, b: u32) -> u32 {
    let mut p = Pair { a, b };
    swap_in_place(&mut p);
    p.a - p.b
}

pub fn double_field(p: &mut Pair) {
    p.a = double(p.a);
}

pub fn doubled_first(a: u32, b: u32) -> u32 {
    let mut p = Pair { a, b };
    double_field(&mut p);
    p.a + p.b
}

pub fn hidden_pair(x: u32) -> u32 {
    let p = Pair { a: x, b: 1 };
    p.a + p.b
}

pub fn after_hidden_pair(x: u32) -> u32 {
    let y = hidden_pair(x);
    y + 1
}

pub trait Area {
    fn area(&self) -> u32;

    fn doubled_area(&self) -> u32 {
        self.area() * 2
    }
}

pub struct Square(pub u32);

pub struct Rect(pub u32, pub u32);

impl Area for Square {
    fn area(&self) -> u32 {
        self.0 * self.0
    }
}

impl Area for Rect {
    fn area(&self) -> u32 {
        self.0 * self.1
    }

    fn doubled_area(&self) -> u32 {
        self.0 * self.1 + self.0 * self.1
    }
}

pub fn square_area(side: u32) -> u32 {
    Square(side).area()
}

pub fn rect_area(w: u32, h: u32) -> u32 {
    Rect(w, h).area()
}

pub fn total_area<T: Area>(a: &T, b: &T) -> u32 {
    a.area() + b.area()
}

pub fn two_squares(x: u32, y: u32) -> u32 {
    total_area(&Square(x), &Square(y))
}

pub fn square_doubled(side: u32) -> u32 {
    Square(side).doubled_area()
}

pub fn rect_doubled(w: u32, h: u32) -> u32 {
    Rect(w, h).doubled_area()
}

pub struct Wrap<T>(pub T);

pub trait Get<T> {
    fn get(&self) -> T;
}

impl<T: Copy> Get<T> for Wrap<T> {
    fn get(&self) -> T {
        self.0
    }
}

pub fn unwrap_u8(x: u8) -> u8 {
    Wrap(x).get()
}

pub fn larger(a: u32, b: u32) -> u32 {
    core::cmp::max(a, b)
}

pub fn exchange(a: u32, b: u32) -> u32 {
    let mut x = a;
    let mut y = b;
    core::mem::swap(&mut x, &mut y);
    x
}

pub fn through_a_local(x: u32) -> u32 {
    let f = double;
    f(x)
}

pub fn spin() -> ! {
    loop {}
}

pub fn call_spin() -> u32 {
    spin()
}

pub fn stop() -> ! {
    std::process::abort()
}

pub fn call_stop() -> u32 {
    stop()
}

pub fn width<const N: u32>() -> u32 {
    N
}

pub fn five() -> u32 {
    width::<5>()
}

pub fn double_n_times(x: u32, n: u32) -> u32 {
    let mut t = x;
    let mut i = 0;
    while i < n {
        t = double(t);
        i += 1;
    }
    t
}

pub trait Choose {
    fn choose<U: Copy>(&self, a: U, b: U) -> U;
}

impl<T: Copy> Choose for Wrap<T> {
    fn choose<U: Copy>(&self, a: U, _b: U) -> U {
        let _kept: T = self.0;
        a
    }
}

pub fn choose_first(flag: bool, a: u16, b: u16) -> u16 {
    Wrap(flag).choose(a, b)
}
