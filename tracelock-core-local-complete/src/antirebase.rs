// src/antirebase.rs
//
// Executable anti-rebase demo.
//
// Rolling hash can rebase a local chunk digest by multiplying one scalar q^s.
// K-Sentry triangular exponents cannot do that in general.
//
// We demonstrate this with shift = 1:
//   T_1 - T_0 = 1
//   T_2 - T_1 = 2
//
// So a scalar that rebases a one-hot event at index 0
// will not also rebase a one-hot event at index 1.

use crate::ksentry::{ksentry_fast, mod_mul, mod_pow};

pub fn ksentry_shifted_spec(xs: &[u128], q: u128, p: u128, shift: u64) -> u128 {
    let mut acc = 0u128;

    for (i, x) in xs.iter().enumerate() {
        let global_i = i as u64 + shift;
        let t = triangular_exp(global_i);
        let w = mod_pow(q, t, p);
        acc = (acc + mod_mul(*x, w, p)) % p;
    }

    acc
}

pub fn triangular_exp(i: u64) -> u128 {
    let i = i as u128;
    i * (i + 1) / 2
}

pub fn fake_scalar_rebase(local_digest: u128, q: u128, p: u128, scalar_exp: u64) -> u128 {
    let scalar = mod_pow(q, scalar_exp as u128, p);
    mod_mul(local_digest, scalar, p)
}

pub fn demo_ksentry_not_one_scalar_rebase(q: u128, p: u128) -> bool {
    let shift = 1u64;

    // one-hot chunk: event at local index 0
    let a = vec![1u128, 0u128];

    // one-hot chunk: event at local index 1
    let b = vec![0u128, 1u128];

    let local_a = ksentry_fast(&a, q, p).digest();
    let local_b = ksentry_fast(&b, q, p).digest();

    let shifted_a = ksentry_shifted_spec(&a, q, p, shift);
    let shifted_b = ksentry_shifted_spec(&b, q, p, shift);

    // If one scalar worked for both, the same scalar exponent would transform both.
    // From a, the needed gap is T_1 - T_0 = 1.
    let scalar_exp_from_a = 1u64;

    let fake_a = fake_scalar_rebase(local_a, q, p, scalar_exp_from_a);
    let fake_b = fake_scalar_rebase(local_b, q, p, scalar_exp_from_a);

    // It should work for a, but fail for b.
    fake_a == shifted_a && fake_b != shifted_b
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ksentry_shifted_spec() {
        let q = 7;
        let p = 1_000_000_007;

        let xs = vec![1, 2, 3];

        let shifted0 = ksentry_shifted_spec(&xs, q, p, 0);
        let local = ksentry_fast(&xs, q, p).digest();

        assert_eq!(shifted0, local);
    }

    #[test]
    fn test_ksentry_not_one_scalar_rebase() {
        let q = 7;
        let p = 1_000_000_007;

        assert!(demo_ksentry_not_one_scalar_rebase(q, p));
    }
}