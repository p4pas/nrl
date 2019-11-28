pub enum Inf {
    Plus,
    Minus
}

pub enum Number {
    NaN,
    Infinite(Inf),
    Finite(BitString),
}

impl Number {
    fn new() -> Number {
        Number {
            v: Finite(BitString::new())
        }
    }
}
