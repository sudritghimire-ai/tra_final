// src/rolling.rs

use crate::ksentry::{mod_add, mod_mul, mod_pow};

#[derive(Debug, Clone)]
pub struct RollingHash {
    pub q: u128,
    pub p: u128,
    pub n: u64,
    pub acc: u128,
    pub weight: u128,
}

impl RollingHash {
    pub fn new(q: u128, p: u128) -> Self {
        assert!(p > 1, "p must be > 1");
        assert!(q > 0, "q must be > 0");

        Self {
            q: q % p,
            p,
            n: 0,
            acc: 0,
            weight: 1,
        }
    }

    pub fn update(&mut self, x: u128) {
        let x = x % self.p;
        self.acc = mod_add(self.acc, mod_mul(x, self.weight, self.p), self.p);
        self.weight = mod_mul(self.weight, self.q, self.p);
        self.n += 1;
    }

    pub fn digest(&self) -> u128 {
        self.acc
    }

    pub fn position(&self) -> u64 {
        self.n
    }
}

pub fn rolling_hash(xs: &[u128], q: u128, p: u128) -> RollingHash {
    let mut st = RollingHash::new(q, p);

    for &x in xs {
        st.update(x);
    }

    st
}

pub fn rolling_shifted_spec(xs: &[u128], q: u128, p: u128, shift: u64) -> u128 {
    let mut acc = 0u128;

    for (i, x) in xs.iter().enumerate() {
        let exp = i as u128 + shift as u128;
        let w = mod_pow(q, exp, p);
        acc = mod_add(acc, mod_mul(*x, w, p), p);
    }

    acc
}

pub fn rolling_rebase_digest(local_digest: u128, q: u128, p: u128, shift: u64) -> u128 {
    let scalar = mod_pow(q, shift as u128, p);
    mod_mul(local_digest, scalar, p)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rolling_order_sensitive() {
        let q = 7;
        let p = 1_000_000_007;

        let a = vec![10, 20, 30, 40];
        let b = vec![10, 30, 20, 40];

        let da = rolling_hash(&a, q, p).digest();
        let db = rolling_hash(&b, q, p).digest();

        assert_ne!(da, db);
    }

    #[test]
    fn test_rolling_scalar_rebase() {
        let q = 7;
        let p = 1_000_000_007;

        let chunk = vec![101, 202, 303, 404];
        let shift = 10;

        let local = rolling_hash(&chunk, q, p).digest();
        let rebased = rolling_rebase_digest(local, q, p, shift);
        let shifted_spec = rolling_shifted_spec(&chunk, q, p, shift);

        assert_eq!(rebased, shifted_spec);
    }

    #[test]
    fn test_rolling_rebase_many_shifts() {
        let q = 7;
        let p = 1_000_000_007;

        let chunk = vec![3, 5, 8, 13, 21];
        let local = rolling_hash(&chunk, q, p).digest();

        for shift in 0..50 {
            let rebased = rolling_rebase_digest(local, q, p, shift);
            let shifted_spec = rolling_shifted_spec(&chunk, q, p, shift);

            assert_eq!(rebased, shifted_spec);
        }
    }
}