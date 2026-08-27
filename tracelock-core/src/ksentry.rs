// src/ksentry.rs
//
// O(1) triangular K-Sentry updater.
// This is the executable version of the Verus invariant:
//
// acc    = Σ x_i q^(T_i) mod p
// weight = q^(T_n) mod p
// step   = q^(n+1) mod p
// T_i    = i(i+1)/2

#[derive(Debug, Clone)]
pub struct KSentry {
    pub q: u128,
    pub p: u128,
    pub n: u64,
    pub acc: u128,
    pub weight: u128,
    pub step: u128,
}

impl KSentry {
    pub fn new(q: u128, p: u128) -> Self {
        assert!(p > 1, "p must be > 1");
        assert!(q > 0, "q must be > 0");

        Self {
            q: q % p,
            p,
            n: 0,
            acc: 0,
            weight: 1, // q^T_0 = q^0 = 1
            step: q % p, // q^(0+1) = q
        }
    }

    pub fn update(&mut self, x: u128) {
        let x = x % self.p;

        // acc' = acc + x_n * q^T_n
        self.acc = mod_add(self.acc, mod_mul(x, self.weight, self.p), self.p);

        // weight' = q^T_n * q^(n+1) = q^T_(n+1)
        self.weight = mod_mul(self.weight, self.step, self.p);

        // step' = q^(n+1) * q = q^(n+2)
        self.step = mod_mul(self.step, self.q, self.p);

        self.n += 1;
    }

    pub fn digest(&self) -> u128 {
        self.acc
    }

    pub fn position(&self) -> u64 {
        self.n
    }

    pub fn checkpoint(&self, stream_id: impl Into<String>, epoch: u64) -> KSCheckpoint {
        KSCheckpoint {
            stream_id: stream_id.into(),
            epoch,
            end_seq: self.n,
            digest: self.acc,
            weight: self.weight,
            step: self.step,
            q: self.q,
            p: self.p,
        }
    }
}

#[derive(Debug, Clone)]
pub struct KSCheckpoint {
    pub stream_id: String,
    pub epoch: u64,
    pub end_seq: u64,
    pub digest: u128,
    pub weight: u128,
    pub step: u128,
    pub q: u128,
    pub p: u128,
}

pub fn triangular_exp(i: u64) -> u128 {
    let i = i as u128;
    i * (i + 1) / 2
}

pub fn mod_pow(mut base: u128, mut exp: u128, p: u128) -> u128 {
    assert!(p > 1, "p must be > 1");

    base %= p;
    let mut result = 1u128;

    while exp > 0 {
        if exp & 1 == 1 {
            result = mod_mul(result, base, p);
        }
        base = mod_mul(base, base, p);
        exp >>= 1;
    }

    result
}

pub fn mod_mul(a: u128, b: u128, p: u128) -> u128 {
    ((a % p) * (b % p)) % p
}

pub fn mod_add(a: u128, b: u128, p: u128) -> u128 {
    ((a % p) + (b % p)) % p
}

// Slow mathematical spec for testing only.
// This recomputes q^(T_i) for every index.
pub fn ksentry_spec(xs: &[u128], q: u128, p: u128) -> u128 {
    let mut acc = 0u128;

    for (i, x) in xs.iter().enumerate() {
        let t = triangular_exp(i as u64);
        let w = mod_pow(q, t, p);
        acc = mod_add(acc, mod_mul(*x, w, p), p);
    }

    acc
}

// Fast O(1) implementation over a whole stream.
pub fn ksentry_fast(xs: &[u128], q: u128, p: u128) -> KSentry {
    let mut st = KSentry::new(q, p);

    for &x in xs {
        st.update(x);
    }

    st
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_triangular_exp() {
        assert_eq!(triangular_exp(0), 0);
        assert_eq!(triangular_exp(1), 1);
        assert_eq!(triangular_exp(2), 3);
        assert_eq!(triangular_exp(3), 6);
        assert_eq!(triangular_exp(4), 10);
    }

    #[test]
    fn test_fast_matches_spec_small() {
        let q = 7;
        let p = 1_000_000_007;
        let xs = vec![3, 9, 12, 99, 5, 8];

        let fast = ksentry_fast(&xs, q, p);
        let slow = ksentry_spec(&xs, q, p);

        assert_eq!(fast.digest(), slow);
        assert_eq!(fast.position(), xs.len() as u64);
    }

    #[test]
    fn test_order_sensitive() {
        let q = 7;
        let p = 1_000_000_007;

        let a = vec![10, 20, 30, 40];
        let b = vec![10, 30, 20, 40];

        let da = ksentry_fast(&a, q, p).digest();
        let db = ksentry_fast(&b, q, p).digest();

        assert_ne!(da, db);
    }

    #[test]
    fn test_checkpoint() {
        let q = 7;
        let p = 1_000_000_007;

        let xs = vec![1, 2, 3];
        let st = ksentry_fast(&xs, q, p);
        let ckpt = st.checkpoint("node-1:exec", 0);

        assert_eq!(ckpt.end_seq, 3);
        assert_eq!(ckpt.digest, st.digest());
        assert_eq!(ckpt.q, q);
        assert_eq!(ckpt.p, p);
    }
}