pub fn id<T>(x: T) -> T {
    x
}

pub fn first<A, B>(a: A, _b: B) -> A {
    a
}

pub fn borrowed<'a, T>(x: &'a T) -> &'a T {
    x
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
