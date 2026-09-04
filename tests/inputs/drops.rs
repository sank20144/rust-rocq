pub struct Noisy(pub u8);

impl Drop for Noisy {
    fn drop(&mut self) {}
}

pub struct Holder<'a> {
    pub r: &'a u8,
    pub n: Noisy,
}

pub fn dangling_field_at_drop() {
    let h;
    {
        let x = 1u8;
        h = Holder { r: &x, n: Noisy(0) };
    }
}

pub fn keep(n: Noisy) -> Noisy {
    let m = n;
    m
}
