pub fn half_up(x: u8) -> u8 {
    x / 2 + x % 2
}

pub fn naive_half_up(x: u8) -> u8 {
    (x + 1) / 2
}
