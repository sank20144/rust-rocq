pub enum Sign {
    Neg,
    Zero,
    Pos,
}

pub fn sign(x: i32) -> Sign {
    if x < 0 {
        Sign::Neg
    } else if x == 0 {
        Sign::Zero
    } else {
        Sign::Pos
    }
}

pub fn weight(s: Sign) -> i32 {
    match s {
        Sign::Neg => -1,
        Sign::Zero => 0,
        Sign::Pos => 1,
    }
}

pub enum Maybe {
    Nothing,
    Just(u32),
}

pub fn unwrap_or(m: Maybe, d: u32) -> u32 {
    match m {
        Maybe::Nothing => d,
        Maybe::Just(v) => v,
    }
}

pub fn incr(m: Maybe) -> Maybe {
    match m {
        Maybe::Nothing => Maybe::Nothing,
        Maybe::Just(v) => Maybe::Just(v + 1),
    }
}
