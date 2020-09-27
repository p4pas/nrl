#![feature(test)]

extern crate test;

use nrl::bitstring::BitString;
// use openssl::bn::BigNum;
use rug::Integer;
// use std::ops::BitAndAssign;

fn and_bitstring(ns: Vec<(BitString, BitString)>) {
    let mut v = Vec::with_capacity(ns.len());
    for (bs0, bs1) in ns.into_iter() {
        v.push(bs0 & bs1);
    }
}

fn and_rugn(ns: Vec<(Integer, Integer)>) {
    let mut v: Vec<Integer> = Vec::with_capacity(ns.len());
    for (bs0, bs1) in ns.into_iter() {
        v.push(bs0 & bs1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::Rng;
    use test::Bencher;

    #[bench]
    fn bench_bitstring(b: &mut Bencher) {
        const S: usize = 1;
        let mut rng = rand::thread_rng();
        for _ in 0..S {
            let bs0 = BitString::from(rng.gen::<u128>());
            let bs1 = BitString::from(rng.gen::<u128>());
            b.iter(|| { let _ = &bs0 ^ &bs1; });
        }
    }

    #[bench]
    fn bench_rug(b: &mut Bencher) {
        const S: usize = 1;
        let mut rng = rand::thread_rng();
        for _ in 0..S {
            let bs0 = Integer::from(rng.gen::<u128>());
            let bs1 = Integer::from(rng.gen::<u128>());
            b.iter(|| { let _: Integer = Integer::from(&bs0) ^ &bs1; });
        }
    }
}
