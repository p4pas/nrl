use std::cmp;
use rand::Rng;

type Bits = u32;
const NBITS: usize = 32;
const NBYTES: usize = 4;
const LOGBITS: usize = 5;
const LOGBYTES: usize = 2;
const ONES: usize = (1 << LOGBITS) - 1;
#[inline(always)]
fn indexes(i: usize) -> (usize, usize) {
    (i >> LOGBITS, i & ONES)
}

#[derive(Clone)]
pub struct BitString {
    bits: Vec<Bits>,
    size: usize,
}

macro_rules! implement_format {
    ( $trait:ty, $format: expr, $length: expr, $one: expr ) => {
        impl $trait for BitString {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let capacity = self.bits.len() + 2;
                let mut v: Vec<String> = Vec::with_capacity(capacity);
                for u in self.bits.iter() {
                    v.push(format!($format, u, w=$length));
                }
                v.push(format!("...{}", if self.limit() { $one } else { '0' }));
                v.push("...".to_string());
                assert_eq!(v.len(), capacity, "{:?}", self); // TODO: Remove
                write!(f, "[{}]", v.join(","))
            }
        }
    }
}

implement_format!(std::fmt::UpperHex, "{:0w$X}", NBITS >> 2, 'F');
implement_format!(std::fmt::LowerHex, "{:0w$x}", NBITS >> 2, 'f');
implement_format!(std::fmt::Binary, "{:0w$b}", NBITS, '1');

impl std::fmt::Debug for BitString {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let capacity = indexes(self.size + 1).0;
        let mut v: Vec<String> = Vec::with_capacity(capacity);
        for u in self.bits.iter() {
            v.push(format!("{:0w$b}", u, w=NBITS).chars().rev().collect());
        }
        v.push(String::from("..."));
        write!(f, "BitString: {{bits: '{}', size: '{}'}}", v.join("|"), self.size)
    }
}

impl BitString {
    pub fn new() -> BitString {
        BitString {
            bits: vec![0],
            size: 0,
        }
    }

    pub fn random(size: usize) -> Self {
        let s = indexes(size).0 + 1;
        let mut bits = Vec::with_capacity(s);
        let mut rng = rand::thread_rng();
        for _ in 0..s {
            bits.push(rng.gen());
        }
        let mut bs = BitString {
            bits,
            size
        };
        bs.set_limit(false);
        bs
    }
    
    #[inline]
    pub fn bit(&self, i: usize) -> bool {
        let (i, j) = indexes(cmp::min(i, self.size));
        self.bits[i] & (1 << j) != 0
    }

    #[inline]
    pub fn bits(&self, i: usize) -> Bits {
        if i <= indexes(self.size).0 {
            self.bits[i]
        } else if self.limit() {
            Bits::max_value()
        } else {
            0
        }
    }

    #[inline]
    pub fn limit(&self) -> bool {
        self.bit(self.size)
    }

    #[inline]
    pub fn set_limit(&mut self, l: bool) -> &mut Self {
        let (i, j) = indexes(self.size);
        let f = (1 << j) - 1;
        if l { self.bits[i] |= !f; }
        else { self.bits[i] &= f; }
        self
    }

    #[inline]
    pub fn resize(&mut self, s: usize) -> &mut Self {
        let l = self.limit();
        let f = if l { Bits::max_value() } else { 0 };
        let r = indexes(s).0 + 1;
        self.bits.resize(r, f);
        self.size = s;
        self.set_limit(l)
    }

    #[inline]
    pub fn set(&mut self, i: usize, b: bool) -> &mut Self {
        if i >= self.size {
            self.resize(i + 1);
        }
        let (i, j) = indexes(i);
        if b { self.bits[i] |= 1 << j; }
        else { self.bits[i] &= !(1 << j); }
        self
    }

    #[inline]
    pub fn flip(&mut self, i: usize) -> &mut Self {
        if i >= self.size {
            self.resize(i + 1);
        }
        let (i, j) = indexes(i);
        self.bits[i] ^= 1 << j;
        self
    }

    #[inline]
    pub fn flip_if(&mut self, i: usize, b: bool) -> &mut Self {
        if self.bit(i) == b {
            self.flip(i);
        }
        self
    }

    #[inline]
    pub fn flip_limit(&mut self) -> &mut Self {
        self.set_limit(!self.limit())
    }

    #[inline]
    pub fn flip_limit_if(&mut self, b: bool) -> &mut Self {
        let l = self.limit();
        if b == l {
            self.set_limit(!l);
        }
        self
    }

    #[inline]
    pub fn compress(&mut self) -> &mut Self {
        let l = self.limit();
        let c = if l { Bits::max_value() } else { 0 };
        let mut i = indexes(self.size).0;
        while i > 0 && self.bits[i] == c {
            i -= 1;
        }
        let mut j = NBITS - 1;
        while j > 0 && (self.bits[i] & 1 << j != 0) == l {
            j -= 1;
        }
        self.resize((i << LOGBITS) + j + 1)
    }

    pub fn weight(&self) -> usize {
        let f = if self.limit() { Bits::count_zeros } else { Bits::count_ones };
        let mut w: usize = 0;
        for b in self.bits.iter() {
            w += f(*b) as usize;
        }
        w
    }
}

impl Ord for BitString {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        let cl = self.limit().cmp(&other.limit());
        match cl {
            cmp::Ordering::Equal => {
                let m = cmp::max(self.bits.len(), other.bits.len());
                for i in (0..m).rev() {
                    let cb = self.bits(i).cmp(&other.bits(i));
                    match cb {
                        cmp::Ordering::Equal => continue,
                        _ => return cb
                    }
                }
                cmp::Ordering::Equal
            },
            _ => cl
        }
    }
}

impl PartialOrd for BitString {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for BitString {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == cmp::Ordering::Equal
    }
}

impl Eq for BitString { }

impl From<&[u8]> for BitString {
    fn from(bytes: &[u8]) -> Self {
        let l = bytes.len();
        let mut bits = vec![0; 1 + (l >> LOGBYTES)];
        for i in (0..bytes.len()).step_by(NBYTES) {
            let mut u = [0; NBYTES];
            let mut j = 0;
            while j < NBYTES && (i + j) < l {
                u[j] = bytes[i + j];
                j += 1;
            }
            bits[i >> LOGBYTES] = u32::from_le_bytes(u);
        }
        BitString {
            bits,
            size: l << 3
        }
    }
}

macro_rules! from_copy {
    ( $f:ident, $( $type:ty ),* ) => {
        $(
            impl From<$type> for BitString {
                fn from(n: $type) -> Self {
                    let bytes = <$type>::$f(n);
                    BitString::from(&bytes[..])
                }
            }
        )*
    }
}

macro_rules! from_reference {
    ( $f:ident, $( $type:ty ),* ) => {
        $(
            impl From<&$type> for BitString {
                fn from(n: &$type) -> Self {
                    let bytes = <$type>::$f(n);
                    BitString::from(&bytes[..])
                }
            }
        )*
    }
}

from_copy!(to_le_bytes, u8, u16, u32, u64, u128, usize);
from_copy!(to_le_bytes, i8, i16, i32, i64, i128, isize);
from_reference!(as_bytes, String, str);

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
        bs.resize(NBITS);
        assert_eq!(bs.size, NBITS);
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

    #[test]
    fn test_display() {
        let mut bs = BitString::new();
        bs.resize(NBITS).set_limit(true);
        let r = |c, n| (0..n).map(|_| c).collect::<String>();
        let z = |n| r("0", n);
        let s = NBITS >> 2;
        assert_eq!(format!("{:X}", bs), format!("[{},{},...F,...]", z(s), r("F", s)));
        assert_eq!(format!("{:x}", bs), format!("[{},{},...f,...]", z(s), r("f", s)));
        assert_eq!(format!("{:b}", bs), format!("[{},{},...1,...]", z(NBITS), r("1", NBITS)));
    }

    #[test]
    fn test_set() {
        let mut bs = BitString::new();
        bs.set(NBITS - 1, true);
        assert_eq!(bs.bits[0], 1 << (NBITS - 1));
        assert_eq!(bs.bits.len(), 2);
        assert_eq!(bs.bits[1], 0);
        bs.set_limit(true);
        assert_eq!(bs.bits[1], Bits::max_value());
        bs.set(NBITS, false);
        assert_eq!(bs.bits[1], Bits::max_value() - 1);
        bs.set(NBITS * 4 - 2, false);
        bs.set_limit(false);
        assert_eq!(bs.bits.len(), 4);       
        assert_eq!(bs.bits[1], Bits::max_value() - 1);
        assert_eq!(bs.bits[2], Bits::max_value());
    }

    #[test]
    fn test_flips() {
        let mut bs = BitString::new();
        bs.flip(NBITS);
        assert_eq!(bs.bits.len(), 2);
        assert_eq!(bs.size, NBITS + 1);
        assert_eq!(bs.bits[0], 0);
        assert_eq!(bs.bits[1], 1);
        bs.flip_if(0, true);
        assert_eq!(bs.bits.len(), 2);
        assert_eq!(bs.size, NBITS + 1);
        assert_eq!(bs.bits[0], 0);
        assert_eq!(bs.bits[1], 1);
        bs.flip_if(0, false);
        assert_eq!(bs.bits[0], 1);
        assert_eq!(bs.bits[1], 1);
        bs.flip_limit();
        assert_eq!(bs.bits[1], Bits::max_value());
        bs.flip_limit_if(false);
        assert_eq!(bs.bits[1], Bits::max_value());
        bs.flip_limit_if(true);
        assert_eq!(bs.bits[1], 1);
    }

    #[test]
    fn test_compress() {
        let mut bs = BitString::new();
        bs.set(NBITS-1, true)
            .set(NBITS, true)
            .resize(10*NBITS - 1)
            .compress()
            .compress();
        assert_eq!(bs.bits.len(), 2);
        assert_eq!(bs.bits[0], 1 << NBITS - 1);
        assert_eq!(bs.bits[1], 1);
        assert_eq!(bs.size, NBITS + 1);
        bs.set_limit(true)
            .compress()
            .compress();
        assert_eq!(bs.bits.len(), 1);
        assert_eq!(bs.bits[0], 1 << NBITS - 1);
    }

    #[test]
    fn test_random() {
        let mut bs = BitString::random(0);
        assert_eq!(bs.bits.len(), 1);
        assert_eq!(bs.bits[0], 0);
        assert_eq!(bs.size, 0);
        bs = BitString::random(3*NBITS - 1);
        assert_eq!(bs.bits.len(), 3);
        assert_eq!(bs.size, 3*NBITS - 1);
    }

    #[test]
    fn test_weight() {
        let mut bs = BitString::new();
        bs.resize(NBITS);
        let w0 = bs.set_limit(true)
                   .resize(2*NBITS)
                   .weight();
        let w1 = bs.set_limit(false).weight();
        assert_eq!(w0, NBITS);
        assert_eq!(w1, NBITS);
    }

    #[test]
    fn test_from_bytes() {
        let mut rng = rand::thread_rng();
        for n in 0..100 {
            let v: Vec<u8> = (0..n).map(|_| { rng.gen::<u8>() }).collect();
            let bs = BitString::from(&v[..]);
            if n == 0 {
                assert_eq!(bs.bits.len(), 1);
                assert_eq!(bs.bits[0], 0);
                assert_eq!(bs.size, 0);
            } else {
                for i in 0..(1 + (v.len() >> 3)) {
                    for j in 0..8 {
                        let b = v[i] & (1 << j) != 0;
                        assert_eq!(b, bs.bit((i << 3) + j));
                    }
                }
            }
        }
    }

    macro_rules! test_from {
        ( $test:ident, $type:ty ) => {
            #[test]
            fn $test() {
                let n: $type = rand::random();
                let bs = BitString::from(n);
                for i in 0..bs.size {
                    assert_eq!(bs.bit(i), n & (1 << i) != 0);
                }
            }
        }
    }

    test_from!(test_from_u8,    u8);
    test_from!(test_from_u16,   u16);
    test_from!(test_from_u32,   u32);
    test_from!(test_from_u64,   u64);
    test_from!(test_from_u128,  u128);
    test_from!(test_from_usize, usize);
    test_from!(test_from_i8,    i8);
    test_from!(test_from_i16,   i16);
    test_from!(test_from_i32,   i32);
    test_from!(test_from_i64,   i64);
    test_from!(test_from_i128,  i128);
    test_from!(test_from_isize, isize);

    #[test]
    fn test_from_string() {
        let mut rng = rand::thread_rng();
        for n in 0..100 {
            let v: String = (0..n).map(|_| { rng.gen::<char>() }).collect();
            let bs0 = BitString::from(&v);
            let bs1 = BitString::from(v.as_str());
            if n == 0 {
                assert_eq!(bs0.bits.len(), 1);
                assert_eq!(bs1.bits.len(), 1);
                assert_eq!(bs0.bits[0], 0);
                assert_eq!(bs1.bits[0], 0);
                assert_eq!(bs0.size, 0);
                assert_eq!(bs1.size, 0);
            } else {
                for i in 0..(1 + (v.len() >> 3)) {
                    for j in 0..8 {
                        let b = v.as_bytes()[i] & (1 << j) != 0;
                        assert_eq!(b, bs0.bit((i << 3) + j));
                        assert_eq!(b, bs1.bit((i << 3) + j));
                    }
                }
            }
        }
    }

    #[test]
    fn test_clone_equality() {
        let bs = BitString::random(10);
        let cbs = bs.clone();
        assert_eq!(bs, cbs);
    }

    #[test]
    fn test_ordering_bit_flip() {
        for i in 0..(NBITS << 2) {
            let bs = BitString::random(i);
            if i == 0 {
                assert_eq!(bs, BitString::from(0));
            } else {
                let mut cbs = bs.clone();
                for j in 0..i {
                    let b = cbs.bit(j);
                    cbs.flip(j);
                    assert_ne!(bs, cbs);
                    cbs.set(j, true);
                    assert!(bs <= cbs);
                    cbs.set(j, false);
                    assert!(bs >= cbs);
                    cbs.set(j, b);
                    assert_eq!(bs, cbs);
                }
            }
        }
    }

    #[test]
    fn test_ordering_limit_flip() {
        for i in 0..(NBITS << LOGBITS) {
            let mut bs = BitString::random(i);
            let mut cbs = bs.clone();
            cbs.set_limit(true);
            bs.resize(2048);
            assert!(bs < cbs);
        }
    }

    #[test]
    fn test_ordering_from_u128() {
        let mut rng = rand::thread_rng();
        for _ in 0..NBITS << LOGBITS {
            let n0: u128 = rng.gen();
            let n1: u128 = rng.gen();
            let bs0 = BitString::from(n0);
            let bs1 = BitString::from(n1);
            assert_eq!(n0.cmp(&n1), bs0.cmp(&bs1));
        }
    }
}
