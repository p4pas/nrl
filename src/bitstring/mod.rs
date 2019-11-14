// use std::ops::{BitAndAssign, BitOrAssign, Not};
// use std::convert::identity;
use std::cmp;

type Bits = u32;
const NBITS: usize = 32;
const LOGBITS: usize = 5;
const ONES: usize = (1 << LOGBITS) - 1;
#[inline(always)]
fn indexes(i: usize) -> (usize, usize) {
    (i >> LOGBITS, i & ONES)
}

pub struct BitString {
    bits: Vec<Bits>,
    size: usize,
}

impl BitString {
    pub fn new() -> BitString {
        BitString {
            bits: vec![0],
            size: 0,
        }
    }

    #[inline]
    fn bit(&self, i: usize) -> bool {
        let (i, j) = indexes(cmp::min(i, self.size));
        self.bits[i] & (1 << j) != 0
    }

    #[inline]
    fn limit(&self) -> bool {
        self.bit(self.size)
    }

    #[inline]
    fn set_limit(&mut self, l: bool) -> &mut Self {
        let (i, j) = indexes(self.size);
        let f = (1 << j) - 1;
        if l { self.bits[i] |= !f; }
        else { self.bits[i] &= f; }
        self
    }

    #[inline]
    fn resize(&mut self, s: usize) -> &mut Self {
        let l = self.limit();
        let f = if l { Bits::max_value() } else { 0 };
        let r = indexes(s + 1).0 + 1;
        self.bits.resize(r, f);
        self.size = s;
        self.set_limit(l)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let bs = BitString::new();
        assert_eq!(bs.bits.len(), 1);
        assert_eq!(bs.bits[0] & 1, 0);
        assert_eq!(bs.size, 0);
    }

    #[test]
    #[should_panic]
    fn test_new_panic() {
        let bs = BitString::new();
        bs.bits[1];
    }

    #[test]
    fn test_access_new() {
        let bs = BitString::new();
        assert_eq!(bs.bit(0), false);
        assert_eq!(bs.bit(1), false);
        assert_eq!(bs.bit(usize::max_value()), false);
    }

    #[test]
    fn test_new_limits() {
        let bs = BitString::new();
        assert_eq!(bs.limit(), false);
        assert_eq!(bs.bit(bs.size), bs.limit());
    }

    #[test]
    fn test_new_set_limit() {
        let mut bs = BitString::new();
        bs.set_limit(true);
        assert_eq!(bs.bits[0], Bits::max_value());
        bs.set_limit(false);
        assert_eq!(bs.bits[0], 0);
    }

    #[test]
    fn test_resize() {
        let mut bs = BitString::new();
        bs.set_limit(true);
        bs.resize(NBITS - 1);
        assert_eq!(bs.size, NBITS - 1);
        assert_eq!(bs.bits.len(), 2);
        assert_eq!(bs.limit(), true);
        assert_eq!(bs.bits[0], Bits::max_value());
        assert_eq!(bs.bits[1], Bits::max_value());
        bs.resize(NBITS - 2);
        assert_eq!(bs.bits.len(), 1);
        assert_eq!(bs.limit(), true);
        assert_eq!(bs.bits[0], Bits::max_value());
        bs.resize(0).set_limit(false);
        assert_eq!(bs.bits.len(), 1);
        assert_eq!(bs.bits[0], 0);
    }

    #[test]
    fn test_limit_after_resize() {
        let mut bs = BitString::new();
        bs.resize(NBITS >> 1).set_limit(true);
        bs.resize(NBITS + (NBITS >> 1)).set_limit(false);
        assert_eq!(bs.bits[0], Bits::max_value() - (1 << (NBITS >> 1)) + 1);
        assert_eq!(bs.bits[1], (1 << (NBITS >> 1)) - 1);
    }
}
