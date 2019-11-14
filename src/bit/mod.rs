//! A module implementing bits and bit operations.
//!
//! This module was implmented mainly for learning purposes.
//! 
//! It provides an `enum` implementation for a bit, and implementations
//! for all binary (`&`, `|`, `^`), and unary (`!`) logical operations.
use std::fmt;
use std::ops::{BitAnd, BitOr, BitXor, Not};

/// An `enum` representation of a bit.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub enum Bit {
    Zero,
    One
}

impl fmt::Display for Bit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", match self {
            Bit::Zero => '0',
            Bit::One => '1'
        })
    }
}

impl BitAnd for Bit {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Bit::Zero, _) => Bit::Zero,
            (_, Bit::Zero) => Bit::Zero,
            _ => Bit::One,
        }
    }
}

impl BitOr for Bit {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Bit::One, _) => Bit::One,
            (_, Bit::One) => Bit::One,
            _ => Bit::Zero
        }
    }
}

impl BitXor for Bit {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        if self == rhs { Bit::Zero }
        else { Bit::One }
    }
}

impl Not for Bit {
    type Output = Self;

    fn not(self) -> Self::Output {
        match self {
            Bit::Zero => Bit::One,
            Bit::One => Bit::Zero
        }
    }
}

macro_rules! from_primitive {
    ( $zero:expr, $( $T:ty ),* ) => {
        $(
            impl From<$T> for Bit {
                    fn from(t: $T) -> Self {
                        if t == $zero { Bit::Zero } 
                        else { Bit::One }
                    }
            }
        )*
    }
}
from_primitive!(0, i8, i16, i32, i64, i128, isize);
from_primitive!(0, u8, u16, u32, u64, u128, usize);
from_primitive!(0.0, f32, f64);
from_primitive!(false, bool);
from_primitive!('\0', char);
impl From<()> for Bit {
    fn from(_:()) -> Self {
        Bit::Zero
    }
}

macro_rules! into_primitive {
    ( $zero:expr, $one:expr, $( $T:ty ),* ) => {
        $(
            impl Into<$T> for Bit {
                fn into(self) -> $T {
                    match self {
                        Bit::Zero => $zero,
                        Bit::One=> $one
                    }
                }
            }
        )*
    }
}
into_primitive!(0, 1, i8, i16, i32, i64, i128, isize);
into_primitive!(0, 1, u8, u16, u32, u64, u128, usize);
into_primitive!(0.0, 1.0, f32, f64);
into_primitive!(false, true, bool);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_display() {
        assert_eq!("0".to_owned(), format!("{}", Bit::Zero));
        assert_eq!("1".to_owned(), format!("{}", Bit::One));
    }

    #[test]
    fn test_and() {
        assert_eq!(Bit::Zero & Bit::Zero, Bit::Zero);
        assert_eq!(Bit::Zero & Bit::One,  Bit::Zero);
        assert_eq!(Bit::One  & Bit::Zero, Bit::Zero);
        assert_eq!(Bit::One  & Bit::One,  Bit::One);
    }

    #[test]
    fn test_or() {
        assert_eq!(Bit::Zero | Bit::Zero, Bit::Zero);
        assert_eq!(Bit::Zero | Bit::One,  Bit::One);
        assert_eq!(Bit::One  | Bit::Zero, Bit::One);
        assert_eq!(Bit::One  | Bit::One,  Bit::One);
    }

    #[test]
    fn test_xor() {
        assert_eq!(Bit::Zero ^ Bit::Zero, Bit::Zero);
        assert_eq!(Bit::Zero ^ Bit::One,  Bit::One);
        assert_eq!(Bit::One  ^ Bit::Zero, Bit::One);
        assert_eq!(Bit::One  ^ Bit::One,  Bit::Zero);
    }

    #[test]
    fn test_not() {
        assert_eq!(!Bit::Zero, Bit::One);
        assert_eq!(!Bit::One, Bit::Zero);
    }

    macro_rules! test_from_primitive {
        ( $test:ident, $T:ty, $zero:expr, $( $values:expr ),* ) => {
            #[test]
            fn $test() {
                let zero: $T = $zero;
                assert_eq!(Bit::from(zero), Bit::Zero);
                $(
                    let value: $T = $values;
                    assert_eq!(Bit::from(value), Bit::One);
                )*
            }
        }
    }
    macro_rules! test_from_signed_primitive {
        ( $test:ident, $T:ty ) => {
            test_from_primitive!($test, $T, 0, 1, 2, 3, <$T>::min_value(), <$T>::max_value());
        }
    }
    macro_rules! test_from_unsigned_primitive {
        ( $test:ident, $T:ty ) => {
            test_from_primitive!($test, $T, <$T>::min_value(), 1, 2, 3, <$T>::max_value());
        }
    }
    test_from_signed_primitive!(test_from_i8,    i8);
    test_from_signed_primitive!(test_from_i16,   i16);
    test_from_signed_primitive!(test_from_i32,   i32);
    test_from_signed_primitive!(test_from_i64,   i64);
    test_from_signed_primitive!(test_from_i128,  i128);
    test_from_signed_primitive!(test_from_isize, isize);
    test_from_unsigned_primitive!(test_from_u8,    u8);
    test_from_unsigned_primitive!(test_from_u16,   u16);
    test_from_unsigned_primitive!(test_from_u32,   u32);
    test_from_unsigned_primitive!(test_from_u64,   u64);
    test_from_unsigned_primitive!(test_from_u128,  u128);
    test_from_unsigned_primitive!(test_from_usize, usize);
    test_from_primitive!(test_from_bool, bool, false, true);
    test_from_primitive!(test_from_char, char, '\0', 'a', 'b', 'z', 'φ');
    #[test]
    fn test_from_unit() {
        assert_eq!(Bit::from(()), Bit::Zero);
    }

    macro_rules! test_into_primitive {
        ( $test:ident, $T:ty, $zero:expr, $one:expr ) => {
            #[test]
            fn $test() {
                let zero: $T = $zero;
                let one: $T = $one;
                assert_eq!(zero, Bit::Zero.into());
                assert_eq!(one, Bit::One.into());
            }
        }
    }
    test_into_primitive!(test_i8,    i8,    0, 1);
    test_into_primitive!(test_i16,   i16,   0, 1);
    test_into_primitive!(test_i32,   i32,   0, 1);
    test_into_primitive!(test_i64,   i64,   0, 1);
    test_into_primitive!(test_i128,  i128,  0, 1);
    test_into_primitive!(test_isize, isize, 0, 1);
    test_into_primitive!(test_u8,    u8,    0, 1);
    test_into_primitive!(test_u16,   u16,   0, 1);
    test_into_primitive!(test_u32,   u32,   0, 1);
    test_into_primitive!(test_u64,   u64,   0, 1);
    test_into_primitive!(test_u128,  u128,  0, 1);
    test_into_primitive!(test_usize, usize, 0, 1);
    test_into_primitive!(test_f32, f32, 0.0, 1.0);
    test_into_primitive!(test_f64, f64, 0.0, 1.0);
}
