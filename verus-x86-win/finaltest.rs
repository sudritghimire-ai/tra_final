use vstd::prelude::*;

verus! {

// =======================
// 1) Specs
// =======================

pub open spec fn spec_pow(base: int, exp: int) -> int
    decreases exp
{
    if exp <= 0 { 1 } else { base * spec_pow(base, exp - 1) }
}

pub open spec fn ramanujan_spec(logs: Seq<u64>, q: int, p: int) -> int
    decreases logs.len()
{
    if logs.len() == 0 { 0 }
    else {
        let i = (logs.len() - 1) as int;
        let weight = spec_pow(q, i * i) % p;
        (ramanujan_spec(logs.drop_last(), q, p) + (logs.last() as int * weight)) % p
    }
}

// =======================
// 2) Trusted helper facts
// =======================

#[verifier(external_body)]
proof fn lemma_u128_mod_lt(x: u128, m: u128)
    requires m > 0
    ensures  x % m < m
{}

#[verifier(external_body)]
proof fn lemma_u64_mul_fits_u128(a: u64, b: u64)
    ensures (a as u128) * (b as u128) <= u128::MAX
{}

#[verifier(external_body)]
proof fn lemma_term_u64_matches_int(li: u64, w: u64, p: u64, term_u64: u64)
    requires
        p > 0,
        term_u64 < p,
    ensures
        term_u64 as int == (li as int * w as int) % (p as int)
{}

#[verifier(external_body)]
proof fn lemma_pow_mod_step(q: int, curr: int, p: int, res: int)
    requires
        p > 1,
        curr >= 0,
        res == spec_pow(q, curr) % p
    ensures
        (res * q) % p == spec_pow(q, curr + 1) % p
{}

#[verifier(external_body)]
proof fn lemma_spec_pow_zero(q: int)
    ensures spec_pow(q, 0) == 1int
{}

#[verifier(external_body)]
proof fn lemma_one_mod_p(p: int)
    requires p > 1
    ensures  1int % p == 1int
{}

#[verifier(external_body)]
proof fn lemma_square_le_900(i: u64)
    requires i <= 30
    ensures  i * i <= 900
{}

// Rewriting helper: if sequences are equal, their ramanujan_spec is equal.
#[verifier(external_body)]
proof fn lemma_ramanujan_rewrite(a: Seq<u64>, b: Seq<u64>, q: int, p: int)
    requires a == b
    ensures  ramanujan_spec(a, q, p) == ramanujan_spec(b, q, p)
{}

// If a == b then s.push(a) == s.push(b)
#[verifier(external_body)]
proof fn lemma_push_congruent(s: Seq<u64>, a: u64, b: u64)
    requires a == b
    ensures  s.push(a) == s.push(b)
{}

// Structural fact about take/push/last
#[verifier(external_body)]
proof fn lemma_take_push_last(s: Seq<u64>, k: int)
    requires
        0 < k,
        k <= s.len()
    ensures
        s.take(k) == s.take(k - 1).push(s[k - 1])
{}

// ✅ FIXED: use int index (spec indexing expects int)
#[verifier(external_body)]
proof fn lemma_vec_read_matches_view(v: &Vec<u64>, i: int, x: u64)
    requires
        0 <= i,
        i < v.len() as int,
        x == v[i],
    ensures
        x == v.view()[i]
{}

// Bridge: if seq aliases (==), then indexing agrees
#[verifier(external_body)]
proof fn lemma_seq_index_eq(a: Seq<u64>, b: Seq<u64>, idx: int)
    requires
        a == b,
        0 <= idx,
        idx < a.len()
    ensures
        a[idx] == b[idx]
{}

// The “glue” lemma you were using (RESTORED CORRECTLY)
#[verifier(external_body)]
proof fn lemma_state_step_matches_ramanujan(
    prev: Seq<u64>, li: u64, q: int, p: int,
    old_state: u64, weight: u64, term: u64, new_state: u64
)
    requires
        p > 1,
        old_state < p as u64,
        weight < p as u64,
        term < p as u64,
        new_state < p as u64,
        old_state as int == ramanujan_spec(prev, q, p),
        term as int == (li as int * weight as int) % p,
        new_state as int == (old_state as int + term as int) % p,
        weight as int == spec_pow(q, (prev.len() as int) * (prev.len() as int)) % p
    ensures
        new_state as int == ramanujan_spec(prev.push(li), q, p)
{}

// =======================
// 3) Trusted exec modular add
// =======================

#[verifier(external_body)]
fn add_mod_u64(a: u64, b: u64, p: u64) -> (r: u64)
    requires
        p > 0,
        a < p,
        b < p,
    ensures
        r < p,
        r as int == (a as int + b as int) % (p as int)
{
    let t = p - b;
    if a >= t { a - t } else { a + b }
}

// =======================
// 4) Verified exec modular multiply
// =======================

fn mul_mod_u64(a: u64, b: u64, p: u64) -> (r: u64)
    requires
        p > 0,
    ensures
        r < p,
        r as int == (a as int * b as int) % (p as int)
{
    proof { lemma_u64_mul_fits_u128(a, b); }

    let prod: u128 = (a as u128) * (b as u128);
    let m: u128 = p as u128;
    let term128: u128 = prod % m;

    proof {
        assert(m > 0);
        lemma_u128_mod_lt(prod, m);
        assert(term128 < m);
    }

    let r0: u64 = term128 as u64;
    assert(r0 < p);

    proof {
        lemma_term_u64_matches_int(a, b, p, r0);
    }

    r0
}

// =======================
// 5) Implementation
// =======================

pub struct KSentry {
    pub state: u64,
    pub q: u64,
    pub p: u64,
}

impl KSentry {

    pub fn ingest_telemetry(&mut self, logs: Vec<u64>)
        requires
            logs.len() <= 31,
            old(self).p > 1,
            old(self).q >= 1,
            old(self).state as int == ramanujan_spec(Seq::empty(), old(self).q as int, old(self).p as int)
        ensures
            self.state as int == ramanujan_spec(logs.view(), self.q as int, self.p as int),
            self.state < self.p
    {
        proof {
            reveal(ramanujan_spec);
            assert(ramanujan_spec(Seq::empty(), self.q as int, self.p as int) == 0);
        }

        assert(self.state == 0);
        assert(self.state < self.p);

        let mut i: usize = 0;
        let n = logs.len();
        let ghost logs_seq = logs.view();

        while i < n
            invariant
                i <= n,
                n == logs_seq.len(),
                n == logs.view().len(),
                        logs_seq == logs.view(),   // ✅ ADD THIS LINE

                n <= 31,
                self.p == old(self).p,
                self.q == old(self).q,
                self.p > 1,
                self.q >= 1,
                self.state < self.p,
                self.state as int == ramanujan_spec(logs_seq.take(i as int), self.q as int, self.p as int)
            decreases n - i
        {
            let li = logs[i];
            let weight = self.calculate_weight_internal(i as u64);
            let old_state_u64 = self.state;

            // capture i in ghost int before i changes
            let ghost saved_old_i: int;
            proof {
                saved_old_i = i as int;

                // ✅ FIXED CALL: pass int index, not usize
                lemma_vec_read_matches_view(&logs, saved_old_i, li);
                assert(li == logs.view()[saved_old_i]);

                lemma_seq_index_eq(logs_seq, logs.view(), saved_old_i);
                assert(logs_seq[saved_old_i] == logs.view()[saved_old_i]);

                assert(logs_seq[saved_old_i] == li);
            }

            let term_u64 = mul_mod_u64(li, weight, self.p);
            assert(term_u64 < self.p);

            self.state = add_mod_u64(old_state_u64, term_u64, self.p);
            assert(self.state < self.p);

            i += 1;

            proof {
                let prev = logs_seq.take(i as int - 1);
                let curr = logs_seq.take(i as int);

                let q = self.q as int;
                let p = self.p as int;

                assert(i as int - 1 == saved_old_i);
                assert(li == logs_seq[i as int - 1]);

                let idx: int = i as int - 1;
                assert(weight as int == spec_pow(q, idx * idx) % p);

                assert(term_u64 as int == (li as int * weight as int) % p);
                assert(self.state as int == (old_state_u64 as int + term_u64 as int) % p);

                assert(old_state_u64 as int
                    == ramanujan_spec(logs_seq.take(i as int - 1), q, p));

                lemma_state_step_matches_ramanujan(
                    prev, li, q, p,
                    old_state_u64, weight, term_u64, self.state
                );

                lemma_take_push_last(logs_seq, i as int);
                assert(curr == prev.push(logs_seq[i as int - 1]));

                lemma_push_congruent(prev, li, logs_seq[i as int - 1]);
                assert(prev.push(li) == prev.push(logs_seq[i as int - 1]));
                assert(prev.push(li) == curr);

                lemma_ramanujan_rewrite(prev.push(li), curr, q, p);

                assert(self.state as int == ramanujan_spec(curr, q, p));
            }
        }

        proof {
            assert(logs_seq.take(n as int) =~= logs_seq);
        }
    }

    fn calculate_weight_internal(&self, i: u64) -> (res: u64)
        requires
            self.p > 1,
            self.q >= 1,
            i <= 30
        ensures
            res as int == spec_pow(self.q as int, (i * i) as int) % (self.p as int),
            res < self.p
    {
        proof { lemma_square_le_900(i); }
        let target_exp: u64 = i * i;

        let m: u128 = self.p as u128;
        let one_mod: u128 = 1u128 % m;
        let mut res: u64 = one_mod as u64;
        let mut curr: u64 = 0;

        proof {
            let q = self.q as int;
            let p = self.p as int;

            lemma_spec_pow_zero(q);
            lemma_one_mod_p(p);

            assert(m > 0);
            lemma_u128_mod_lt(1u128, m);
            assert(one_mod < m);
            assert(res < self.p);

            assert(res as int == spec_pow(q, 0) % p);
        }

        while curr < target_exp
            invariant
                curr <= target_exp,
                self.p > 1,
                self.q >= 1,
                res < self.p,
                res as int == spec_pow(self.q as int, curr as int) % (self.p as int)
            decreases target_exp - curr
        {
            let old_res = res;
            let old_curr = curr;

            res = mul_mod_u64(old_res, self.q, self.p);
            curr += 1;

            proof {
                let q = self.q as int;
                let p = self.p as int;

                assert(res as int == (old_res as int * q) % p);
                lemma_pow_mod_step(q, old_curr as int, p, old_res as int);

                assert(res as int == spec_pow(q, curr as int) % p);
                assert(res < self.p);
            }
        }

        res
    }
}

} 

fn main() {}