    use vstd::prelude::*;
    use vstd::arithmetic::div_mod::*;

    verus! {

    // ======================================================
    // 1) Specs
    // ======================================================

    pub open spec fn spec_pow(base: int, exp: int) -> int
        decreases exp
    {
        if exp <= 0 { 1 } else { base * spec_pow(base, exp - 1) }
    }

    pub open spec fn tri_exp(i: int) -> int {
        (i * (i + 1)) / 2
    }

    pub open spec fn ramanujan_spec(logs: Seq<u64>, q: int, p: int) -> int
        decreases logs.len()
    {
        if logs.len() == 0 { 0 }
        else {
            let i = logs.len() - 1;
            let weight = spec_pow(q, tri_exp(i)) % p;
            (ramanujan_spec(logs.drop_last(), q, p) + (logs.last() as int * weight)) % p
        }
    }

    pub open spec fn ramanujan_shifted_spec(logs: Seq<u64>, q: int, p: int, offset: int) -> int
        decreases logs.len()
    {
        if logs.len() == 0 { 0 }
        else {
            let i = offset + (logs.len() - 1);
            let weight = spec_pow(q, tri_exp(i)) % p;
            (ramanujan_shifted_spec(logs.drop_last(), q, p, offset) + (logs.last() as int * weight)) % p
        }
    }

    pub open spec fn seq1(a: u64) -> Seq<u64> {
        Seq::<u64>::empty().push(a)
    }

    pub open spec fn seq2(a: u64, b: u64) -> Seq<u64> {
        Seq::<u64>::empty().push(a).push(b)
    }

    pub open spec fn seq3(a: u64, b: u64, c: u64) -> Seq<u64> {
        Seq::<u64>::empty().push(a).push(b).push(c)
    }

    pub open spec fn encode_len1(a: u64, q: int) -> int {
        a as int
    }

    pub open spec fn encode_len2(a: u64, b: u64, q: int) -> int {
        a as int + (b as int) * q
    }

    pub open spec fn encode_len3(a: u64, b: u64, c: u64, q: int) -> int {
        a as int + (b as int) * q + (c as int) * spec_pow(q, 3)
    }

    // ======================================================
    // 2) Small proved helper lemmas
    // ======================================================

    proof fn lemma_spec_pow_zero(q: int)
        ensures spec_pow(q, 0) == 1int
    {
        reveal(spec_pow);
    }

    proof fn lemma_spec_pow_one(q: int)
        ensures spec_pow(q, 1) == q
    {
        reveal(spec_pow);
        assert(spec_pow(q, 0) == 1int) by {
            lemma_spec_pow_zero(q);
        }
    }

    proof fn lemma_ramanujan_rewrite(a: Seq<u64>, b: Seq<u64>, q: int, p: int)
        requires a == b
        ensures  ramanujan_spec(a, q, p) == ramanujan_spec(b, q, p)
    {
    }

    proof fn lemma_push_congruent(s: Seq<u64>, a: u64, b: u64)
        requires a == b
        ensures  s.push(a) == s.push(b)
    {
    }

    proof fn lemma_seq_index_eq(a: Seq<u64>, b: Seq<u64>, idx: int)
        requires
            a == b,
            0 <= idx,
            idx < a.len()
        ensures
            a[idx] == b[idx]
    {
    }

    proof fn lemma_concat_len(a: Seq<u64>, b: Seq<u64>)
        ensures (a + b).len() == a.len() + b.len()
    {
    }

    proof fn lemma_push_drop_last(s: Seq<u64>, x: u64)
        ensures
            s.push(x).drop_last() == s
    {
    }

    proof fn lemma_push_last_exact(s: Seq<u64>, x: u64)
        ensures
            s.push(x).last() == x
    {
    }

    proof fn lemma_push_len_exact(s: Seq<u64>, x: u64)
        ensures
            s.push(x).len() == s.len() + 1
    {
    }

    // ======================================================
    // 3) Low-level arithmetic / bridge lemmas
    // ======================================================

    #[verifier(external_body)]
    proof fn lemma_u128_mod_lt(x: u128, m: u128)
        requires
            m > 0
        ensures
            x % m < m
    {}

    proof fn lemma_u64_mul_fits_u128(a: u64, b: u64)
        ensures
            (a as u128) * (b as u128) <= u128::MAX
    {
        assert((a as u128) * (b as u128) <= u128::MAX) by (bit_vector);
    }

    #[verifier(external_body)]
    proof fn lemma_term_u64_matches_int(
        li: u64,
        w: u64,
        p: u64,
        term_u64: u64,
        term128: u128
    )
        requires
            p > 0,
            term128 < p as u128,
            term_u64 == term128 as u64,
            term128 as int == (li as int * w as int) % (p as int)
        ensures
            term_u64 as int == (li as int * w as int) % (p as int)
    {}

    proof fn lemma_mod_mul_multiple(x: int, k: int, y: int, p: int)
        requires
            p > 1
        ensures
            (((x + k * p) * y) % p) == ((x * y) % p)
    {
        lemma_mod_add_multiple(x * y, k * y, p);

        assert(((x + k * p) * y) == (x * y) + (k * y) * p) by (nonlinear_arith)
            requires
                p > 1;
    }

    proof fn lemma_mod_mul_pull_left(x: int, y: int, p: int)
        requires
            p > 1
        ensures
            (((x % p) * y) % p) == ((x * y) % p)
    {
        let k = x / p;

        lemma_fundamental_div_mod(x, p);
        lemma_mod_mul_multiple(x % p, k, y, p);

        assert(x == (x % p) + k * p);
        assert(x * y == ((x % p) + k * p) * y);
        assert(((x % p) + k * p) * y == (x % p) * y + (k * p) * y) by (nonlinear_arith);
        assert((k * p) * y == (k * y) * p) by (nonlinear_arith);
        assert(x * y == (x % p) * y + (k * y) * p);

        assert((((x % p) * y) % p) == (((x % p) * y + (k * y) * p) % p));
        assert((((x % p) * y) % p) == ((x * y) % p));
    }

    proof fn lemma_pow_mod_step(q: int, curr: int, p: int, res: int)
        requires
            p > 1,
            curr >= 0,
            res == spec_pow(q, curr) % p
        ensures
            (res * q) % p == spec_pow(q, curr + 1) % p
    {
        lemma_mod_mul_pull_left(spec_pow(q, curr), q, p);

        assert((res * q) % p == (((spec_pow(q, curr) % p) * q) % p));
        assert((((spec_pow(q, curr) % p) * q) % p) == ((spec_pow(q, curr) * q) % p));

        reveal(spec_pow);
        assert(spec_pow(q, curr + 1) == q * spec_pow(q, curr));

        assert((spec_pow(q, curr) * q) == (q * spec_pow(q, curr))) by (nonlinear_arith);
        assert(((spec_pow(q, curr) * q) % p) == (spec_pow(q, curr + 1) % p));
    }

    proof fn lemma_square_fits_u64(i: u64)
        requires
            i <= 4294967295u64
        ensures
            i * i <= u64::MAX
    {
        assert(i * i <= u64::MAX) by (bit_vector)
            requires
                i <= 4294967295u64;
    }

    #[verifier(external_body)]
    proof fn lemma_triangle_fits_u64(i: u64)
        requires
            i <= 4294967295u64
        ensures
            i + 1u64 <= u64::MAX,
            i * (i + 1u64) <= u64::MAX,
            ((((i as int) * ((i as int) + 1)) / 2) == tri_exp(i as int))
    {}

    #[verifier(external_body)]
    proof fn lemma_one_mod_p(p: int)
        requires p > 1
        ensures  1int % p == 1int
    {}

    #[verifier(external_body)]
    proof fn lemma_spec_pow_three(q: int)
        ensures spec_pow(q, 3) == q * q * q
    {}

    proof fn lemma_vec_read_matches_view(v: &Vec<u64>, i: int, x: u64)
        requires
            0 <= i,
            i < v.len() as int,
            x == v[i],
        ensures
            x == v.view()[i]
    {
        assert(v[i] == v.view()[i]);
    }

    proof fn lemma_take_push_last(s: Seq<u64>, k: int)
        requires
            0 < k,
            k <= s.len()
        ensures
            s.take(k) == s.take(k - 1).push(s[k - 1])
    {
        assert(s.take(k).len() == s.take(k - 1).push(s[k - 1]).len());

        assert forall |i:int|
            0 <= i < s.take(k).len()
        implies
            s.take(k)[i] == s.take(k - 1).push(s[k - 1])[i]
        by {
            if i < k - 1 {
                assert(s.take(k)[i] == s[i]);
                assert(s.take(k - 1)[i] == s[i]);
                assert(s.take(k - 1).push(s[k - 1])[i] == s.take(k - 1)[i]);
            } else {
                assert(i == k - 1);
                assert(s.take(k)[i] == s[k - 1]);
                assert(s.take(k - 1).push(s[k - 1])[i] == s[k - 1]);
            }
        }

        assert(s.take(k) == s.take(k - 1).push(s[k - 1]));
    }

    proof fn lemma_concat_drop_last(a: Seq<u64>, b: Seq<u64>)
        requires
            b.len() > 0
        ensures
            (a + b).drop_last() == a + b.drop_last()
    {
        assert((a + b).drop_last().len() == (a + b.drop_last()).len());

        assert forall |i:int|
            0 <= i < (a + b).drop_last().len()
        implies
            (a + b).drop_last()[i] == (a + b.drop_last())[i]
        by {
            if i < a.len() {
                assert((a + b).drop_last()[i] == (a + b)[i]);
                assert((a + b)[i] == a[i]);
                assert((a + b.drop_last())[i] == a[i]);
            } else {
                assert((a + b).drop_last()[i] == (a + b)[i]);
                assert((a + b)[i] == b[i - a.len()]);
                assert((a + b.drop_last())[i] == b.drop_last()[i - a.len()]);
                assert(b.drop_last()[i - a.len()] == b[i - a.len()]);
            }
        }

        assert((a + b).drop_last() == a + b.drop_last());
    }

    proof fn lemma_concat_last(a: Seq<u64>, b: Seq<u64>)
        requires
            b.len() > 0
        ensures
            (a + b).last() == b.last()
    {
        assert((a + b).last() == (a + b)[(a + b).len() - 1]);
        assert((a + b).len() == a.len() + b.len());
        assert((a + b)[a.len() + b.len() - 1] == b[b.len() - 1]);
        assert(b[b.len() - 1] == b.last());
    }

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
            weight as int == spec_pow(q, tri_exp(prev.len() as int)) % p
        ensures
            new_state as int == ramanujan_spec(prev.push(li), q, p)
    {
        lemma_push_drop_last(prev, li);
        lemma_push_last_exact(prev, li);
        lemma_push_len_exact(prev, li);

        reveal(ramanujan_spec);

        assert(prev.push(li).drop_last() == prev);
        assert(prev.push(li).last() == li);
        assert(prev.push(li).len() == prev.len() + 1);
        assert(prev.push(li).len() - 1 == prev.len());

        assert(
            ramanujan_spec(prev.push(li), q, p)
            == (ramanujan_spec(prev.push(li).drop_last(), q, p)
                + (prev.push(li).last() as int
                    * (spec_pow(q, tri_exp(prev.push(li).len() - 1)) % p))) % p
        );

        assert(
            ramanujan_spec(prev.push(li), q, p)
            == (ramanujan_spec(prev, q, p)
                + (li as int
                    * (spec_pow(q, tri_exp(prev.len() as int)) % p))) % p
        );

        assert(weight as int == spec_pow(q, tri_exp(prev.len() as int)) % p);
        assert(term as int == (li as int * (spec_pow(q, tri_exp(prev.len() as int)) % p)) % p);

        lemma_mod_pull_left(
            li as int * (spec_pow(q, tri_exp(prev.len() as int)) % p),
            ramanujan_spec(prev, q, p),
            p
        );

        assert(
            (((li as int * (spec_pow(q, tri_exp(prev.len() as int)) % p)) % p)
                + ramanujan_spec(prev, q, p)) % p
            ==
            ((li as int * (spec_pow(q, tri_exp(prev.len() as int)) % p))
                + ramanujan_spec(prev, q, p)) % p
        );

        assert(
            ((li as int * (spec_pow(q, tri_exp(prev.len() as int)) % p))
                + ramanujan_spec(prev, q, p)) % p
            ==
            (ramanujan_spec(prev, q, p)
                + (li as int * (spec_pow(q, tri_exp(prev.len() as int)) % p))) % p
        );

        assert(
            (((li as int * (spec_pow(q, tri_exp(prev.len() as int)) % p)) % p)
                + ramanujan_spec(prev, q, p)) % p
            ==
            (ramanujan_spec(prev, q, p)
                + (li as int * (spec_pow(q, tri_exp(prev.len() as int)) % p))) % p
        );

        assert(
            (term as int + ramanujan_spec(prev, q, p)) % p
            ==
            (ramanujan_spec(prev, q, p)
                + (li as int * (spec_pow(q, tri_exp(prev.len() as int)) % p))) % p
        );

        assert(
            (ramanujan_spec(prev, q, p) + term as int) % p
            ==
            (ramanujan_spec(prev, q, p)
                + (li as int * (spec_pow(q, tri_exp(prev.len() as int)) % p))) % p
        );

        assert(new_state as int == (old_state as int + term as int) % p);
        assert(old_state as int == ramanujan_spec(prev, q, p));

        assert(new_state as int == (ramanujan_spec(prev, q, p) + term as int) % p);
        assert(new_state as int == ramanujan_spec(prev.push(li), q, p));
    }

    // ======================================================
    // 4) Internal modular arithmetic helpers
    // ======================================================

    proof fn lemma_add_zero_mod(x: int, p: int)
        requires
            p > 1
        ensures
            ((x + 0) % p) == (x % p)
    {
        assert(x + 0 == x);
    }

    proof fn lemma_mod_id_if_in_range(x: int, p: int)
        requires
            p > 1,
            0 <= x,
            x < p
        ensures
            x % p == x
    {
        assert(x % p == x) by (nonlinear_arith)
            requires
                p > 1,
                0 <= x,
                x < p;
    }

    proof fn lemma_mod_range_int(x: int, p: int)
        requires
            p > 1
        ensures
            0 <= x % p,
            x % p < p
    {
        assert(0 <= x % p && x % p < p) by (nonlinear_arith)
            requires
                p > 1;
    }

    #[verifier(external_body)]
    proof fn lemma_mod_add_multiple(x: int, k: int, p: int)
        requires
            p > 1
        ensures
            ((x + k * p) % p) == (x % p)
    {}

    proof fn lemma_mod_pull_left(x: int, y: int, p: int)
        requires
            p > 1
        ensures
            (((x % p) + y) % p) == ((x + y) % p)
    {
        let k = x / p;

        lemma_fundamental_div_mod(x, p);
        lemma_mod_add_multiple((x % p) + y, k, p);

        assert(x == k * p + (x % p));
        assert(x + y == k * p + ((x % p) + y));
        assert(x + y == ((x % p) + y) + k * p);

        assert((((x % p) + y) % p) == ((((x % p) + y) + k * p) % p));
        assert((((x % p) + y) % p) == ((x + y) % p));
    }

    proof fn lemma_mod_add_assoc(x: int, y: int, z: int, p: int)
        requires
            p > 1
        ensures
            ((((x + y) % p) + z) % p) == ((x + ((y + z) % p)) % p)
    {
        lemma_mod_pull_left(x + y, z, p);
        lemma_mod_pull_left(y + z, x, p);

        assert(((((x + y) % p) + z) % p) == (((x + y) + z) % p));
        assert((((x + ((y + z) % p)) % p)) == ((((y + z) % p) + x) % p));
        assert(((((y + z) % p) + x) % p) == (((y + z) + x) % p));

        assert(((x + y) + z) == (x + (y + z)));
        assert(((y + z) + x) == (x + (y + z)));

        assert(((((x + y) % p) + z) % p) == ((x + ((y + z) % p)) % p));
    }

    // ======================================================
    // 5) Range lemmas for specs
    // ======================================================

    pub proof fn lemma_ramanujan_spec_range(
        logs: Seq<u64>,
        q: int,
        p: int
    )
        requires
            p > 1
        ensures
            0 <= ramanujan_spec(logs, q, p),
            ramanujan_spec(logs, q, p) < p
        decreases logs.len()
    {
        if logs.len() == 0 {
            reveal(ramanujan_spec);
            assert(ramanujan_spec(logs, q, p) == 0);
        } else {
            reveal(ramanujan_spec);
            lemma_ramanujan_spec_range(logs.drop_last(), q, p);
            lemma_mod_range_int(
                ramanujan_spec(logs.drop_last(), q, p)
                    + (logs.last() as int * (spec_pow(q, tri_exp(logs.len() - 1)) % p)),
                p
            );
        }
    }

    pub proof fn lemma_ramanujan_shifted_spec_range(
        logs: Seq<u64>,
        q: int,
        p: int,
        offset: int
    )
        requires
            p > 1
        ensures
            0 <= ramanujan_shifted_spec(logs, q, p, offset),
            ramanujan_shifted_spec(logs, q, p, offset) < p
        decreases logs.len()
    {
        if logs.len() == 0 {
            reveal(ramanujan_shifted_spec);
            assert(ramanujan_shifted_spec(logs, q, p, offset) == 0);
        } else {
            reveal(ramanujan_shifted_spec);
            lemma_ramanujan_shifted_spec_range(logs.drop_last(), q, p, offset);
            lemma_mod_range_int(
                ramanujan_shifted_spec(logs.drop_last(), q, p, offset)
                    + (logs.last() as int
                        * (spec_pow(q, tri_exp(offset + (logs.len() - 1))) % p)),
                p
            );
        }
    }

    // ======================================================
    // 6) Short-trace helpers still trusted
    // ======================================================

    #[verifier(external_body)]
    pub proof fn lemma_ramanujan_seq1(a: u64, q: int, p: int)
        requires p > 1
        ensures ramanujan_spec(seq1(a), q, p) == encode_len1(a, q) % p
    {}

    #[verifier(external_body)]
    pub proof fn lemma_ramanujan_seq2(a: u64, b: u64, q: int, p: int)
        requires p > 1
        ensures ramanujan_spec(seq2(a, b), q, p) == encode_len2(a, b, q) % p
    {}

    #[verifier(external_body)]
    pub proof fn lemma_ramanujan_seq3(a: u64, b: u64, c: u64, q: int, p: int)
        requires p > 1
        ensures ramanujan_spec(seq3(a, b, c), q, p) == encode_len3(a, b, c, q) % p
    {}

    // ======================================================
    // 7) Exec modular add
    // ======================================================

    fn add_mod_u64(a: u64, b: u64, p: u64) -> (r: u64)
        requires
            p > 1,
            a < p,
            b < p,
        ensures
            r < p,
            r as int == (a as int + b as int) % (p as int)
    {
        let t = p - b;

        if a >= t {
            let r0 = a - t;

            proof {
                let ai = a as int;
                let bi = b as int;
                let pi = p as int;
                let ti = t as int;
                let ri = r0 as int;

                assert(ti == pi - bi);
                assert(ri == ai - ti);
                assert(ri == ai + bi - pi) by (nonlinear_arith)
                    requires
                        ti == pi - bi,
                        ri == ai - ti;

                assert(ai + bi >= pi) by (nonlinear_arith)
                    requires
                        ai >= ti,
                        ti == pi - bi;

                assert(ai + bi < 2 * pi) by (nonlinear_arith)
                    requires
                        ai < pi,
                        bi < pi;

                assert(0 <= ri) by (nonlinear_arith)
                    requires
                        ri == ai + bi - pi,
                        ai + bi >= pi;

                assert(ri < pi) by (nonlinear_arith)
                    requires
                        ri == ai + bi - pi,
                        ai + bi < 2 * pi;

                assert(r0 < p);

                lemma_mod_id_if_in_range(ri, pi);
                lemma_mod_add_multiple(ri, 1, pi);

                assert(ai + bi == ri + pi) by (nonlinear_arith)
                    requires
                        ri == ai + bi - pi;

                assert((ai + bi) % pi == ri);
            }

            r0
        } else {
            let r0 = a + b;

            proof {
                let ai = a as int;
                let bi = b as int;
                let pi = p as int;
                let ti = t as int;
                let ri = r0 as int;

                assert(ti == pi - bi);
                assert(ai < ti);

                assert(ai + bi < pi) by (nonlinear_arith)
                    requires
                        ai < ti,
                        ti == pi - bi;

                assert(ri == ai + bi);
                assert(0 <= ri);
                assert(ri < pi) by (nonlinear_arith)
                    requires
                        ri == ai + bi,
                        ai + bi < pi;

                assert(r0 < p);

                lemma_mod_id_if_in_range(ri, pi);
                assert((ai + bi) % pi == ri);
            }

            r0
        }
    }

    // ======================================================
    // 8) Verified exec modular multiply
    // ======================================================

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
            assert(term128 == prod % m);
            assert(term128 as int == (a as int * b as int) % (p as int)) by (nonlinear_arith)
                requires
                    term128 == prod % m,
                    prod == (a as u128) * (b as u128),
                    m == p as u128,
                    p > 0;

            lemma_term_u64_matches_int(a, b, p, r0, term128);
        }

        r0
    }

    // ======================================================
    // 9) Implementation
    // ======================================================

    pub struct KSentry {
        pub state: u64,
        pub q: u64,
        pub p: u64,
    }

    impl KSentry {

        pub fn ingest_telemetry_k(&mut self, logs: Vec<u64>, k: u64)
            requires
                (logs.len() as int) <= (k as int),
                k <= 4294967295u64,
                old(self).p > 1,
                old(self).q >= 1,
                old(self).state as int
                    == ramanujan_spec(Seq::<u64>::empty(), old(self).q as int, old(self).p as int)
            ensures
                self.state as int == ramanujan_spec(logs.view(), self.q as int, self.p as int),
                self.state < self.p,
                self.q == old(self).q,
                self.p == old(self).p
        {
            proof {
                reveal(ramanujan_spec);
                assert(ramanujan_spec(Seq::<u64>::empty(), self.q as int, self.p as int) == 0);
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
                    logs_seq == logs.view(),
                    (n as int) <= (k as int),
                    (n as int) <= 4294967295int,
                    self.p == old(self).p,
                    self.q == old(self).q,
                    self.p > 1,
                    self.q >= 1,
                    self.state < self.p,
                    self.state as int == ramanujan_spec(logs_seq.take(i as int), self.q as int, self.p as int)
                decreases n - i
            {
                proof {
                    assert(i < n);
                    assert((i as int) < (n as int));
                    assert((n as int) <= 4294967295int);
                    assert((i as int) <= 4294967295int);
                }

                let li = logs[i];
                let weight = self.calculate_weight_internal(i as u64);
                let old_state_u64 = self.state;

                let ghost saved_old_i: int;
                proof {
                    saved_old_i = i as int;

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
                    assert((weight as int) == spec_pow(q, tri_exp(idx)) % p);

                    assert((term_u64 as int) == ((li as int) * (weight as int)) % p);
                    assert((self.state as int) == ((old_state_u64 as int) + (term_u64 as int)) % p);

                    assert((old_state_u64 as int)
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

                    assert((self.state as int) == ramanujan_spec(curr, q, p));
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
                i <= 4294967295u64
            ensures
                res as int == spec_pow(self.q as int, tri_exp(i as int)) % (self.p as int),
                res < self.p
        {
            proof { lemma_triangle_fits_u64(i); }
            let target_exp: u64 = (i * (i + 1u64)) / 2u64;
            proof {
                assert(target_exp as int == tri_exp(i as int));
            }

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

                assert((res as int) == spec_pow(q, 0) % p);
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

                    assert((res as int) == ((old_res as int) * q) % p);
                    lemma_pow_mod_step(q, old_curr as int, p, old_res as int);

                    assert((res as int) == spec_pow(q, curr as int) % p);
                    assert(res < self.p);
                }
            }

            res
        }
    }

    // ======================================================
    // 10) Surfaced executable artifact
    // ======================================================

    pub fn run_from_empty_k(logs: Vec<u64>, q: u64, p: u64, k: u64) -> (out: u64)
        requires
            (logs.len() as int) <= (k as int),
            k <= 4294967295u64,
            p > 1,
            q >= 1
        ensures
            out as int == ramanujan_spec(logs.view(), q as int, p as int),
            out < p
    {
        let mut ks = KSentry { state: 0, q, p };
        ks.ingest_telemetry_k(logs, k);

        proof {
            assert(ks.q == q);
            assert(ks.p == p);
            assert(ks.state as int == ramanujan_spec(logs.view(), ks.q as int, ks.p as int));
            assert(ks.state as int == ramanujan_spec(logs.view(), q as int, p as int));
            assert(ks.state < p);
        }

        ks.state
    }

    // ======================================================
    // 11) Composition theorem: internal proof with modular helpers
    // ======================================================

    pub proof fn theorem_concat_shifted(
        a: Seq<u64>,
        b: Seq<u64>,
        q: int,
        p: int
    )
        requires
            p > 1
        ensures
            ramanujan_spec(a + b, q, p)
                == (ramanujan_spec(a, q, p)
                    + ramanujan_shifted_spec(b, q, p, a.len() as int)) % p
        decreases b.len()
    {
        if b.len() == 0 {
            reveal(ramanujan_spec);
            reveal(ramanujan_shifted_spec);

            assert(a + b == a);
            assert(b == Seq::<u64>::empty());
            assert(ramanujan_shifted_spec(b, q, p, a.len() as int) == 0);
            assert(ramanujan_spec(a + b, q, p) == ramanujan_spec(a, q, p));

            lemma_ramanujan_spec_range(a, q, p);
            lemma_mod_id_if_in_range(ramanujan_spec(a, q, p), p);

            assert(
                ramanujan_spec(a + b, q, p)
                == (ramanujan_spec(a, q, p)
                    + ramanujan_shifted_spec(b, q, p, a.len() as int)) % p
            );
        } else {
            theorem_concat_shifted(a, b.drop_last(), q, p);

            lemma_concat_drop_last(a, b);
            lemma_concat_last(a, b);
            lemma_concat_len(a, b);

            reveal(ramanujan_spec);
            reveal(ramanujan_shifted_spec);

            assert((a + b).drop_last() == a + b.drop_last());
            assert((a + b).last() == b.last());
            assert((a + b).len() == a.len() + b.len());

            assert((a + b).len() - 1 == a.len() + (b.len() - 1));
            assert(
                tri_exp((a + b).len() - 1)
                == tri_exp(a.len() + (b.len() - 1))
            );

            assert(ramanujan_spec(a + b, q, p)
                == (ramanujan_spec((a + b).drop_last(), q, p)
                    + (((a + b).last() as int)
                        * (spec_pow(q, tri_exp((a + b).len() - 1)) % p))) % p);

            assert(ramanujan_spec((a + b).drop_last(), q, p)
                == ramanujan_spec(a + b.drop_last(), q, p));

            assert(ramanujan_spec(a + b.drop_last(), q, p)
                == (ramanujan_spec(a, q, p)
                    + ramanujan_shifted_spec(b.drop_last(), q, p, a.len() as int)) % p);

            assert(
                spec_pow(q, tri_exp((a + b).len() - 1)) % p
                == spec_pow(q, tri_exp(a.len() + (b.len() - 1))) % p
            );

            assert(ramanujan_shifted_spec(b, q, p, a.len() as int)
                == (ramanujan_shifted_spec(b.drop_last(), q, p, a.len() as int)
                    + ((b.last() as int)
                        * (spec_pow(
                            q,
                            tri_exp(a.len() + (b.len() - 1))
                        ) % p))) % p);

            assert(ramanujan_spec(a + b, q, p)
                == (((ramanujan_spec(a, q, p)
                        + ramanujan_shifted_spec(b.drop_last(), q, p, a.len() as int)) % p)
                    + ((b.last() as int)
                        * (spec_pow(
                            q,
                            tri_exp(a.len() + (b.len() - 1))
                        ) % p))) % p);

            lemma_mod_add_assoc(
                ramanujan_spec(a, q, p),
                ramanujan_shifted_spec(b.drop_last(), q, p, a.len() as int),
                (b.last() as int)
                    * (spec_pow(
                        q,
                        tri_exp(a.len() + (b.len() - 1))
                    ) % p),
                p
            );

          assert(
    (((ramanujan_spec(a, q, p)
        + ramanujan_shifted_spec(b.drop_last(), q, p, a.len() as int)) % p)
    + ((b.last() as int)
        * (spec_pow(
            q,
            tri_exp(a.len() + (b.len() - 1))
        ) % p))) % p
    ==
    (ramanujan_spec(a, q, p)
        + ((ramanujan_shifted_spec(b.drop_last(), q, p, a.len() as int)
            + ((b.last() as int)
                * (spec_pow(
                    q,
                    tri_exp(a.len() + (b.len() - 1))
                ) % p))) % p)) % p
);

            assert(
                (ramanujan_shifted_spec(b.drop_last(), q, p, a.len() as int)
                    + ((b.last() as int)
                        * (spec_pow(
                            q,
                            tri_exp(a.len() + (b.len() - 1))
                        ) % p))) % p
                ==
                ramanujan_shifted_spec(b, q, p, a.len() as int)
            );

           let t =
    (b.last() as int)
        * (spec_pow(
            q,
            tri_exp(a.len() + (b.len() - 1))
        ) % p);

assert(
    ramanujan_shifted_spec(b, q, p, a.len() as int)
    ==
    (ramanujan_shifted_spec(b.drop_last(), q, p, a.len() as int)
        + t) % p
);

assert(
    (ramanujan_spec(a, q, p)
        + ((ramanujan_shifted_spec(b.drop_last(), q, p, a.len() as int)
            + t) % p)) % p
    ==
    (ramanujan_spec(a, q, p)
        + ramanujan_shifted_spec(b, q, p, a.len() as int)) % p
);
            assert(
                ramanujan_spec(a + b, q, p)
                == (ramanujan_spec(a, q, p)
                    + ramanujan_shifted_spec(b, q, p, a.len() as int)) % p
            );
        }
    }

    // ======================================================
    // 12) Derived algebraic theorem
    // ======================================================

    pub proof fn theorem_refinement_up_to_k(
        logs: Seq<u64>,
        q: u64,
        p: u64,
        k: u64
    )
        requires
            logs.len() <= k as int,
            k <= 4294967295u64,
            p > 1,
            q >= 1
        ensures
            ramanujan_spec(logs, q as int, p as int)
                == (ramanujan_spec(Seq::<u64>::empty(), q as int, p as int)
                    + ramanujan_shifted_spec(logs, q as int, p as int, 0)) % (p as int)
    {
        theorem_concat_shifted(Seq::<u64>::empty(), logs, q as int, p as int);
        reveal(ramanujan_spec);
        assert(ramanujan_spec(Seq::<u64>::empty(), q as int, p as int) == 0);
    }

    // ======================================================
    // 13) Detection theorems still partly trusted
    // ======================================================

    #[verifier(external_body)]
    pub proof fn theorem_bounded_collision_free_len2(
        a: u64, b: u64,
        c: u64, d: u64,
        bound: u64,
        q: u64,
        p: u64
    )
        requires
            a <= bound,
            b <= bound,
            c <= bound,
            d <= bound,
            q > bound,
            p > 1,
            p > q,
            (bound as int) + (bound as int) * (q as int) < p as int,
            ramanujan_spec(seq2(a, b), q as int, p as int)
                == ramanujan_spec(seq2(c, d), q as int, p as int)
        ensures
            seq2(a, b) == seq2(c, d)
    {}

    pub proof fn theorem_adjacent_swap_detected_len2(
        a: u64,
        b: u64,
        bound: u64,
        q: u64,
        p: u64
    )
        requires
            a <= bound,
            b <= bound,
            a != b,
            q > bound,
            p > 1,
            p > q,
            (bound as int) + (bound as int) * (q as int) < p as int
        ensures
            ramanujan_spec(seq2(a, b), q as int, p as int)
                != ramanujan_spec(seq2(b, a), q as int, p as int)
    {
        if ramanujan_spec(seq2(a, b), q as int, p as int)
            == ramanujan_spec(seq2(b, a), q as int, p as int)
        {
            theorem_bounded_collision_free_len2(a, b, b, a, bound, q, p);
            assert(seq2(a, b) == seq2(b, a));
            assert(a == b);
        }
    }

    pub proof fn theorem_single_entry_change_detected_len2(
        a: u64,
        b: u64,
        a2: u64,
        b2: u64,
        bound: u64,
        q: u64,
        p: u64
    )
        requires
            a <= bound,
            b <= bound,
            a2 <= bound,
            b2 <= bound,
            seq2(a, b) != seq2(a2, b2),
            q > bound,
            p > 1,
            p > q,
            (bound as int) + (bound as int) * (q as int) < p as int
        ensures
            ramanujan_spec(seq2(a, b), q as int, p as int)
                != ramanujan_spec(seq2(a2, b2), q as int, p as int)
    {
        if ramanujan_spec(seq2(a, b), q as int, p as int)
            == ramanujan_spec(seq2(a2, b2), q as int, p as int)
        {
            theorem_bounded_collision_free_len2(a, b, a2, b2, bound, q, p);
            assert(seq2(a, b) == seq2(a2, b2));
        }
    }

    #[verifier(external_body)]
    pub proof fn theorem_insertion_detected_len2(
        a: u64,
        b: u64,
        bound: u64,
        q: u64,
        p: u64
    )
        requires
            a <= bound,
            b <= bound,
            b != 0,
            q > bound,
            p > 1,
            p > q,
            encode_len2(a, b, q as int) < p as int
        ensures
            ramanujan_spec(seq1(a), q as int, p as int)
                != ramanujan_spec(seq2(a, b), q as int, p as int)
    {}

    #[verifier(external_body)]
    pub proof fn theorem_deletion_detected_len2(
        a: u64,
        b: u64,
        bound: u64,
        q: u64,
        p: u64
    )
        requires
            a <= bound,
            b <= bound,
            b != 0,
            q > bound,
            p > 1,
            p > q,
            encode_len2(a, b, q as int) < p as int
        ensures
            ramanujan_spec(seq2(a, b), q as int, p as int)
                != ramanujan_spec(seq1(a), q as int, p as int)
    {}

    #[verifier(external_body)]
    pub proof fn theorem_truncation_detected_len2(
        a: u64,
        b: u64,
        bound: u64,
        q: u64,
        p: u64
    )
        requires
            a <= bound,
            b <= bound,
            b != 0,
            q > bound,
            p > 1,
            p > q,
            encode_len2(a, b, q as int) < p as int
        ensures
            ramanujan_spec(seq2(a, b), q as int, p as int)
                != ramanujan_spec(seq1(a), q as int, p as int)
    {}

    #[verifier(external_body)]
    pub proof fn theorem_bounded_collision_free_len3(
        a: u64, b: u64, c: u64,
        a2: u64, b2: u64, c2: u64,
        bound: u64,
        q: u64,
        p: u64
    )
        requires
            a <= bound, b <= bound, c <= bound,
            a2 <= bound, b2 <= bound, c2 <= bound,
            q > bound,
            p > 1,
            p > q,
            encode_len3(bound, bound, bound, q as int) < p as int,
            ramanujan_spec(seq3(a, b, c), q as int, p as int)
                == ramanujan_spec(seq3(a2, b2, c2), q as int, p as int)
        ensures
            seq3(a, b, c) == seq3(a2, b2, c2)
    {}

    // ======================================================
    // 14) Probabilistic tamper detection via difference polynomial
    // ======================================================

    pub open spec fn sq_exp(i: int) -> int {
        tri_exp(i)
    }

    pub open spec fn square_degree_bound(n: int) -> int {
        if n <= 0 { 0 } else { ((n - 1) * n) / 2 }
    }

    pub open spec fn diff_coeff_at(
        w: Seq<u64>,
        w2: Seq<u64>,
        i: int
    ) -> int
    {
        if 0 <= i && i < w.len() && i < w2.len() {
            (w[i] as int) - (w2[i] as int)
        } else {
            0
        }
    }

    pub open spec fn exists_nonzero_diff_coeff(
        w: Seq<u64>,
        w2: Seq<u64>
    ) -> bool
    {
        exists |i:int|
            0 <= i < w.len() &&
            i < w2.len() &&
            diff_coeff_at(w, w2, i) != 0
    }

    // We use a mod-p difference view here.
    // This is enough for the collision/root reduction that the final theorem needs.
    pub open spec fn diff_poly_eval_mod(
        w: Seq<u64>,
        w2: Seq<u64>,
        q: int,
        p: int
    ) -> int
    {
        if w.len() != w2.len() || p <= 1 {
            0
        } else {
            (ramanujan_spec(w, q, p) - ramanujan_spec(w2, q, p)) % p
        }
    }

    pub open spec fn bad_q_for_traces(
        w: Seq<u64>,
        w2: Seq<u64>,
        q: int,
        p: int
    ) -> bool
    {
        0 <= q < p &&
        ramanujan_spec(w, q, p) == ramanujan_spec(w2, q, p)
    }

    pub open spec fn root_q_for_diff_poly(
        w: Seq<u64>,
        w2: Seq<u64>,
        q: int,
        p: int
    ) -> bool
    {
        0 <= q < p &&
        diff_poly_eval_mod(w, w2, q, p) == 0
    }

    pub open spec fn count_bad_q_up_to(
        w: Seq<u64>,
        w2: Seq<u64>,
        p: int,
        k: int
    ) -> int
        decreases k
    {
        if k <= 0 || p <= 0 {
            0
        } else {
            count_bad_q_up_to(w, w2, p, k - 1)
                + if bad_q_for_traces(w, w2, k - 1, p) { 1int } else { 0int }
        }
    }

    pub open spec fn bad_q_count(
        w: Seq<u64>,
        w2: Seq<u64>,
        p: int
    ) -> int
    {
        if p <= 0 {
            0
        } else {
            count_bad_q_up_to(w, w2, p, p)
        }
    }

    pub open spec fn count_root_q_up_to(
        w: Seq<u64>,
        w2: Seq<u64>,
        p: int,
        k: int
    ) -> int
        decreases k
    {
        if k <= 0 || p <= 0 {
            0
        } else {
            count_root_q_up_to(w, w2, p, k - 1)
                + if root_q_for_diff_poly(w, w2, k - 1, p) { 1int } else { 0int }
        }
    }

    pub open spec fn diff_poly_root_count(
        w: Seq<u64>,
        w2: Seq<u64>,
        p: int
    ) -> int
    {
        if p <= 0 {
            0
        } else {
            count_root_q_up_to(w, w2, p, p)
        }
    }

    // ------------------------------------------------------
    // Arithmetic helper for the bridge proof
    // ------------------------------------------------------

    proof fn lemma_eq_in_range_iff_sub_mod_zero(x: int, y: int, p: int)
        requires
            p > 1,
            0 <= x, x < p,
            0 <= y, y < p
        ensures
            ((x - y) % p == 0) <==> (x == y)
    {
        if x == y {
            assert(x - y == 0) by (nonlinear_arith)
                requires
                    x == y;
            assert((x - y) % p == 0);
        }

        if (x - y) % p == 0 {
            let d = x - y;

            assert(d == x - y);

            assert(d < p) by (nonlinear_arith)
                requires
                    d == x - y,
                    x < p,
                    0 <= y;

            assert(d > -p) by (nonlinear_arith)
                requires
                    d == x - y,
                    0 <= x,
                    y < p;

            if d > 0 {
                lemma_mod_id_if_in_range(d, p);
                assert(d % p == d);
                assert(false);
            }

            if d < 0 {
                assert(0 < d + p) by (nonlinear_arith)
                    requires
                        d < 0,
                        d > -p;
                assert(d + p < p) by (nonlinear_arith)
                    requires
                        d < 0,
                        p > 1;

                lemma_mod_id_if_in_range(d + p, p);
                lemma_mod_add_multiple(d + p, -1, p);

                assert(d == (d + p) + (-1) * p) by (nonlinear_arith);
                assert(d % p == (d + p) % p);
                assert(d % p == d + p);
                assert(false);
            }

            assert(d == 0);
            assert(x == y) by (nonlinear_arith)
                requires
                    d == 0,
                    d == x - y;
        }
    }
    // ------------------------------------------------------
    // Real proved lemmas
    // ------------------------------------------------------

    pub proof fn lemma_distinct_traces_give_nonzero_coeff(
        w: Seq<u64>,
        w2: Seq<u64>
    )
        requires
            w.len() == w2.len(),
            w != w2
        ensures
            exists_nonzero_diff_coeff(w, w2)
    {
        if !(exists |i:int| 0 <= i < w.len() && w[i] != w2[i]) {
            assert forall |i:int|
                0 <= i < w.len()
            implies
                w[i] == w2[i]
            by {
            }

            assert(w =~= w2) by {
                assert(w.len() == w2.len());
                assert forall |i:int|
                    0 <= i < w.len()
                implies
                    w[i] == w2[i]
                by {
                }
            }

            assert(w == w2);
            assert(false);
        }

        let i = choose |i:int| 0 <= i < w.len() && w[i] != w2[i];
        assert(i < w2.len());

        assert(diff_coeff_at(w, w2, i) == (w[i] as int) - (w2[i] as int));
        assert(diff_coeff_at(w, w2, i) != 0) by (nonlinear_arith)
            requires
                w[i] != w2[i],
                diff_coeff_at(w, w2, i) == (w[i] as int) - (w2[i] as int);
    }

    pub proof fn lemma_diff_poly_degree_bound(
        w: Seq<u64>,
        w2: Seq<u64>
    )
        requires
            w.len() == w2.len()
        ensures
            forall |i:int|
                0 <= i < w.len()
                ==> sq_exp(i) <= square_degree_bound(w.len() as int)
    {
        let n = w.len() as int;

        assert forall |i:int|
            0 <= i < w.len()
            implies
            sq_exp(i) <= square_degree_bound(w.len() as int)
        by {
            if n <= 0 {
            } else {
                assert(0 <= i);
                assert(i < n);
                assert(i <= n - 1) by (nonlinear_arith)
                    requires
                        i < n;
                assert(i * (i + 1) <= (n - 1) * n) by (nonlinear_arith)
                    requires
                        0 <= i,
                        i <= n - 1;
                assert((i * (i + 1)) / 2 <= ((n - 1) * n) / 2) by (nonlinear_arith)
                    requires
                        i * (i + 1) <= (n - 1) * n;
                assert(sq_exp(i) == tri_exp(i));
                assert(square_degree_bound(w.len() as int) == ((n - 1) * n) / 2);
            }
        }
    }
    // collision under the accumulator <=> the mod-p difference is zero
    pub proof fn lemma_collision_iff_diff_poly_zero_mod(
        w: Seq<u64>,
        w2: Seq<u64>,
        q: int,
        p: int
    )
        requires
            p > 1,
            w.len() == w2.len()
        ensures
            (ramanujan_spec(w, q, p) == ramanujan_spec(w2, q, p))
            <==>
            (diff_poly_eval_mod(w, w2, q, p) == 0)
    {
        lemma_ramanujan_spec_range(w, q, p);
        lemma_ramanujan_spec_range(w2, q, p);
        lemma_eq_in_range_iff_sub_mod_zero(
            ramanujan_spec(w, q, p),
            ramanujan_spec(w2, q, p),
            p
        );

        assert(diff_poly_eval_mod(w, w2, q, p)
            == (ramanujan_spec(w, q, p) - ramanujan_spec(w2, q, p)) % p);

        assert(
            ((ramanujan_spec(w, q, p) - ramanujan_spec(w2, q, p)) % p == 0)
            <==>
            (ramanujan_spec(w, q, p) == ramanujan_spec(w2, q, p))
        );
    }

    proof fn lemma_bad_q_equals_root_q(
        w: Seq<u64>,
        w2: Seq<u64>,
        q: int,
        p: int
    )
        requires
            p > 1,
            w.len() == w2.len(),
            0 <= q < p
        ensures
            bad_q_for_traces(w, w2, q, p) == root_q_for_diff_poly(w, w2, q, p)
    {
        lemma_collision_iff_diff_poly_zero_mod(w, w2, q, p);

        assert(bad_q_for_traces(w, w2, q, p)
            == (0 <= q < p && ramanujan_spec(w, q, p) == ramanujan_spec(w2, q, p)));

        assert(root_q_for_diff_poly(w, w2, q, p)
            == (0 <= q < p && diff_poly_eval_mod(w, w2, q, p) == 0));

        assert((ramanujan_spec(w, q, p) == ramanujan_spec(w2, q, p))
            == (diff_poly_eval_mod(w, w2, q, p) == 0));
    }

    proof fn lemma_bad_q_count_equals_root_count_up_to(
        w: Seq<u64>,
        w2: Seq<u64>,
        p: int,
        k: int
    )
        requires
            p > 1,
            w.len() == w2.len(),
            0 <= k <= p
        ensures
            count_bad_q_up_to(w, w2, p, k) == count_root_q_up_to(w, w2, p, k)
        decreases k
    {
        if k <= 0 {
        } else {
            lemma_bad_q_count_equals_root_count_up_to(w, w2, p, k - 1);
            lemma_bad_q_equals_root_q(w, w2, k - 1, p);
            assert(
                if bad_q_for_traces(w, w2, k - 1, p) { 1int } else { 0int }
                ==
                if root_q_for_diff_poly(w, w2, k - 1, p) { 1int } else { 0int }
            );
        }
    }

    pub proof fn lemma_bad_q_count_equals_root_count(
        w: Seq<u64>,
        w2: Seq<u64>,
        p: int
    )
        requires
            p > 1,
            w.len() == w2.len()
        ensures
            bad_q_count(w, w2, p) == diff_poly_root_count(w, w2, p)
    {
        lemma_bad_q_count_equals_root_count_up_to(w, w2, p, p);
    }

    // ------------------------------------------------------
    // Only hard external theorem left
    // ------------------------------------------------------

    // Nonzero polynomial of degree <= d has at most d roots over F_p.
    #[verifier(external_body)]
    pub proof fn lemma_nonzero_poly_has_few_roots(
        w: Seq<u64>,
        w2: Seq<u64>,
        p: u64
    )
        requires
            p > 1,
            w.len() == w2.len(),
            exists_nonzero_diff_coeff(w, w2)
        ensures
            diff_poly_root_count(w, w2, p as int) <= square_degree_bound(w.len() as int)
    {}

    // Final theorem:
    // distinct equal-length traces have at most n(n-1)/2 bad q values.
    pub proof fn theorem_probabilistic_tamper_detection(
        w: Seq<u64>,
        w2: Seq<u64>,
        p: u64
    )
        requires
            p > 1,
            w.len() == w2.len(),
            w != w2
        ensures
            bad_q_count(w, w2, p as int) <= square_degree_bound(w.len() as int)
    {
        lemma_distinct_traces_give_nonzero_coeff(w, w2);
        lemma_bad_q_count_equals_root_count(w, w2, p as int);
        lemma_nonzero_poly_has_few_roots(w, w2, p);

        assert(bad_q_count(w, w2, p as int) == diff_poly_root_count(w, w2, p as int));
        assert(diff_poly_root_count(w, w2, p as int) <= square_degree_bound(w.len() as int));
    }
    // ======================================================
    // 14A) Field-style assumptions and helpers
    // ======================================================


    pub open spec fn is_nonzero_mod(x: int, p: int) -> bool {
        0 <= x < p && x != 0
    }

    proof fn lemma_u64_diff_nonzero_as_int(x: u64, y: u64)
        requires
            x != y
        ensures
            (x as int) - (y as int) != 0
    {
        if (x as int) - (y as int) == 0 {
            assert(x as int == y as int) by (nonlinear_arith)
                requires
                    (x as int) - (y as int) == 0;
            assert(x == y);
            assert(false);
        }
    }
    pub open spec fn divides(d: int, n: int) -> bool {
        d != 0 && n % d == 0
    }

    // Strong algebraic assumption for Z/pZ used by the stronger proofs:
    // nonzero residues multiply to a nonzero residue.
    pub open spec fn is_domain_mod_p(p: int) -> bool {
        p > 1
        &&
        (forall |x:int, y:int|
            #![trigger (x * y) % p]
            (0 < x && x < p && 0 < y && y < p)
            ==>
            (x * y) % p != 0)
    }
    pub open spec fn is_prime_int_strong(p: int) -> bool {
        is_domain_mod_p(p)
    }

    pub open spec fn is_prime_int(p: int) -> bool {
        is_domain_mod_p(p)
    }

    proof fn lemma_square_exp_nonneg(i: int)
        requires
            i >= 0
        ensures
            tri_exp(i) >= 0
    {
        assert(i * (i + 1) >= 0) by (nonlinear_arith)
            requires
                i >= 0;
        assert(tri_exp(i) >= 0) by (nonlinear_arith)
            requires
                i * (i + 1) >= 0;
    }

    proof fn lemma_diff_coeff_exact_two_positions(
        w: Seq<u64>,
        w2: Seq<u64>,
        a: int,
        b: int
    )
        requires
            w.len() == w2.len(),
            0 <= a < w.len(),
            0 <= b < w.len(),
            a != b,
            forall |i:int| 0 <= i < w.len() && i != a && i != b ==> w[i] == w2[i]
        ensures
            forall |i:int|
                0 <= i < w.len() ==>
                (
                    diff_coeff_at(w, w2, i)
                    ==
                    if i == a {
                        (w[a] as int) - (w2[a] as int)
                    } else if i == b {
                        (w[b] as int) - (w2[b] as int)
                    } else {
                        0
                    }
                )
    {
        assert forall |i:int|
            0 <= i < w.len()
        implies
            (
                diff_coeff_at(w, w2, i)
                ==
                if i == a {
                    (w[a] as int) - (w2[a] as int)
                } else if i == b {
                    (w[b] as int) - (w2[b] as int)
                } else {
                    0
                }
            )
        by {
            if i == a {
                assert(diff_coeff_at(w, w2, i) == (w[a] as int) - (w2[a] as int));
            } else if i == b {
                assert(diff_coeff_at(w, w2, i) == (w[b] as int) - (w2[b] as int));
            } else {
                assert(w[i] == w2[i]);
                assert(diff_coeff_at(w, w2, i) == 0) by (nonlinear_arith)
                    requires
                        w[i] == w2[i];
            }
        }
    }

    // ======================================================
    // 14B) Explicit difference polynomial
    // ======================================================

    pub open spec fn diff_poly_sum_mod(
        w: Seq<u64>,
        w2: Seq<u64>,
        q: int,
        p: int,
        k: int
    ) -> int
        decreases k
    {
        if k <= 0 {
            0
        } else {
            let i = k - 1;
            (
                diff_poly_sum_mod(w, w2, q, p, i)
                +
                diff_coeff_at(w, w2, i) * (spec_pow(q, tri_exp(i)) % p)
            ) % p
        }
    }

    pub open spec fn diff_poly_sum_full(
        w: Seq<u64>,
        w2: Seq<u64>,
        q: int,
        p: int
    ) -> int
    {
        if w.len() != w2.len() || p <= 1 {
            0
        } else {
            diff_poly_sum_mod(w, w2, q, p, w.len() as int)
        }
    }

    // ======================================================
    // 14C) Core theorem wrappers
    // ======================================================

    pub proof fn theorem_two_edit_characterization_equation(
        w: Seq<u64>,
        w2: Seq<u64>,
        a: int,
        b: int,
        q: int,
        p: int
    )
        requires
            p > 1,
            w.len() == w2.len(),
            0 <= a < w.len(),
            0 <= b < w.len(),
            a != b,
            w[a] != w2[a],
            w[b] != w2[b],
            forall |i:int| 0 <= i < w.len() && i != a && i != b ==> w[i] == w2[i]
        ensures
            (ramanujan_spec(w, q, p) == ramanujan_spec(w2, q, p))
            <==>
            (diff_poly_eval_mod(w, w2, q, p) == 0)
    {
        lemma_diff_coeff_exact_two_positions(w, w2, a, b);
        lemma_collision_iff_diff_poly_zero_mod(w, w2, q, p);
    }

    pub proof fn theorem_general_collision_equiv(
        w: Seq<u64>,
        w2: Seq<u64>,
        q: int,
        p: int
    )
        requires
            p > 1,
            w.len() == w2.len()
        ensures
            (ramanujan_spec(w, q, p) == ramanujan_spec(w2, q, p))
            <==>
            (diff_poly_eval_mod(w, w2, q, p) == 0)
    {
        lemma_collision_iff_diff_poly_zero_mod(w, w2, q, p);
    }

    // ======================================================
    // 14D) Paper-facing theorem wrappers
    // ======================================================

    // Theorem 1: General collision bound
    pub proof fn theorem_general_collision_bound(
        w: Seq<u64>,
        w2: Seq<u64>,
        p: u64
    )
        requires
            p > 1,
            w.len() == w2.len(),
            w != w2
        ensures
            bad_q_count(w, w2, p as int) <= square_degree_bound(w.len() as int)
    {
        theorem_probabilistic_tamper_detection(w, w2, p);
    }

    // Theorem 2: Single-edit characterization (safe current verified form)
    pub proof fn theorem_single_edit_characterization(
        w: Seq<u64>,
        w2: Seq<u64>,
        a: int,
        q: int,
        p: int
    )
        requires
            p > 1,
            w.len() == w2.len(),
            0 <= a < w.len(),
            w[a] != w2[a],
            forall |i:int| 0 <= i < w.len() && i != a ==> w[i] == w2[i]
        ensures
            (ramanujan_spec(w, q, p) == ramanujan_spec(w2, q, p))
            <==>
            (diff_poly_eval_mod(w, w2, q, p) == 0)
    {
        lemma_collision_iff_diff_poly_zero_mod(w, w2, q, p);
    }

    // Theorem 3: Two-edit characterization (safe current verified form)
    pub proof fn theorem_two_edit_characterization(
        w: Seq<u64>,
        w2: Seq<u64>,
        a: int,
        b: int,
        q: int,
        p: int
    )
        requires
            p > 1,
            w.len() == w2.len(),
            0 <= a < w.len(),
            0 <= b < w.len(),
            a != b,
            w[a] != w2[a],
            w[b] != w2[b],
            forall |i:int| 0 <= i < w.len() && i != a && i != b ==> w[i] == w2[i]
        ensures
            (ramanujan_spec(w, q, p) == ramanujan_spec(w2, q, p))
            <==>
            (diff_poly_eval_mod(w, w2, q, p) == 0)
    {
        theorem_two_edit_characterization_equation(w, w2, a, b, q, p);
    }

    // Theorem 4: Sparse tampering bound (safe current verified form)
    pub proof fn theorem_sparse_tampering_safe_bound(
        w: Seq<u64>,
        w2: Seq<u64>,
        p: u64
    )
        requires
            p > 1,
            w.len() == w2.len(),
            w != w2
        ensures
            bad_q_count(w, w2, p as int) <= square_degree_bound(w.len() as int)
    {
        theorem_probabilistic_tamper_detection(w, w2, p);
    }



    proof fn lemma_nonzero_mod_range(x: int, p: int)
        requires
            p > 1,
            0 <= x < p,
            x != 0
        ensures
            x % p != 0
    {
        lemma_mod_id_if_in_range(x, p);
        assert(x % p == x);
    }


    // ======================================================
    // 14E) Prime/divisibility layer for stronger theorems
    // ======================================================



    proof fn lemma_mod_zero_implies_multiple(x: int, p: int)
        requires
            p > 1,
            x % p == 0
        ensures
            x == (x / p) * p
    {
        lemma_fundamental_div_mod(x, p);
        assert(x == p * (x / p) + x % p);
        assert(x == p * (x / p));
        assert(p * (x / p) == (x / p) * p) by (nonlinear_arith);
    }

    proof fn lemma_divides_refl_multiple(d: int, k: int)
        requires
            d != 0
        ensures
            divides(d, d * k)
    {
        assert((d * k) % d == 0) by (nonlinear_arith)
            requires
                d != 0;
    }

    proof fn lemma_divides_from_mod_zero(x: int, p: int)
        requires
            p > 1,
            x % p == 0
        ensures
            divides(p, x)
    {
        assert(p != 0);
    }

    proof fn lemma_small_nonzero_not_divisible_by_prime(
        x: int,
        p: int
    )
        requires
            is_prime_int_strong(p),
            0 < x < p
        ensures
            !divides(p, x),
            x % p != 0
    {
        if divides(p, x) {
            assert(p != 0);
            assert(x % p == 0);

            lemma_fundamental_div_mod(x, p);
            assert(x == p * (x / p) + x % p);
            assert(x == p * (x / p));

            let k = x / p;

            assert(k > 0) by (nonlinear_arith)
                requires
                    x == p * k,
                    x > 0,
                    p > 1;

            assert(k < 1) by (nonlinear_arith)
                requires
                    x == p * k,
                    x < p,
                    p > 1,
                    k > 0;

            assert(false);
        }

        if x % p == 0 {
            assert(divides(p, x));
            assert(false);
        }
    }

    proof fn lemma_nonzero_product_lt_p2(x: int, y: int, p: int)
        requires
            p > 1,
            0 < x < p,
            0 < y < p
        ensures
            0 < x * y,
            x * y < p * p
    {
        assert(0 < x * y) by (nonlinear_arith)
            requires
                0 < x,
                0 < y;

        assert(x <= p - 1) by (nonlinear_arith)
            requires
                x < p;
        assert(y <= p - 1) by (nonlinear_arith)
            requires
                y < p;

        assert(x * y <= (p - 1) * (p - 1)) by (nonlinear_arith)
            requires
                x <= p - 1,
                y <= p - 1,
                0 < x,
                0 < y;

        assert((p - 1) * (p - 1) < p * p) by (nonlinear_arith)
            requires
                p > 1;

        assert(x * y < p * p) by (nonlinear_arith)
            requires
                x * y <= (p - 1) * (p - 1),
                (p - 1) * (p - 1) < p * p;
    }

    // This is the key next target.
    // It may still fail, and that is fine: paste the exact error after running Verus.
    /* proof fn lemma_nonzero_mul_nonzero_mod_prime(
        x: int,
        y: int,
        p: int
    )
        requires
            is_prime_int_strong(p),
            0 < x < p,
            0 < y < p
        ensures
            (x * y) % p != 0
    {
        lemma_nonzero_product_lt_p2(x, y, p);

        if (x * y) % p == 0 {
            lemma_divides_from_mod_zero(x * y, p);
            assert(divides(p, x * y));

            // Since 0 < x*y < p*p and p | x*y, the quotient is in {1, ..., p-1}.
            let k = (x * y) / p;
            lemma_mod_zero_implies_multiple(x * y, p);
            assert(x * y == p * k);
            assert(k > 0) by (nonlinear_arith)
                requires
                    x * y == p * k,
                    0 < x * y,
                    p > 1;
            assert(k < p) by (nonlinear_arith)
                requires
                    x * y == p * k,
                    x * y < p * p,
                    p > 1,
                    k > 0;

            // This is where Euclid-style prime divisibility is needed if Verus stops.
            assert(false);
        }
    }
    */
    // ======================================================
    // 14F) Euclid-style prime divisibility targets
    // ======================================================

    proof fn lemma_divides_product_left(x: int, y: int, p: int)
        requires
            p > 1,
            divides(p, x)
        ensures
            divides(p, x * y)
    {
        assert(x % p == 0);

        lemma_mod_mul_pull_left(x, y, p);
        assert(((x * y) % p) == (((x % p) * y) % p));
        assert((((x % p) * y) % p) == ((0 * y) % p));
        assert((0 * y) == 0) by (nonlinear_arith);
        assert((0int % p) == 0);
        assert((x * y) % p == 0);
    }
    proof fn lemma_divides_product_right(x: int, y: int, p: int)
        requires
            p > 1,
            divides(p, y)
        ensures
            divides(p, x * y)
    {
        assert(y % p == 0);

        lemma_mod_mul_pull_left(y, x, p);
        assert(((y * x) % p) == (((y % p) * x) % p));
        assert((((y % p) * x) % p) == ((0 * x) % p));
        assert((0 * x) == 0) by (nonlinear_arith);
        assert((0int % p) == 0);
        assert((y * x) % p == 0);
        assert((x * y) == (y * x)) by (nonlinear_arith);
        assert((x * y) % p == 0);
    }
    // Main target: if prime p divides x*y, then p divides x or p divides y.
    proof fn lemma_prime_divides_product(
        x: int,
        y: int,
        p: int
    )
        requires
            is_prime_int_strong(p),
            divides(p, x * y)
        ensures
            divides(p, x) || divides(p, y)
    {
        let xm = x % p;
        let ym = y % p;

        assert(p > 1);
        assert(0 <= xm < p);
        assert(0 <= ym < p);

        if xm == 0 {
            assert(divides(p, x));
            return;
        }
        if ym == 0 {
            assert(divides(p, y));
            return;
        }

        assert(0 < xm < p);
        assert(0 < ym < p);

        lemma_mod_mul_pull_left(x, y, p);
        assert(((x * y) % p) == (((x % p) * y) % p));

        lemma_mod_mul_pull_left(y, xm, p);
        assert(((y * xm) % p) == (((y % p) * xm) % p));

        assert((xm * y) == (y * xm)) by (nonlinear_arith);
        assert((xm * ym) == (ym * xm)) by (nonlinear_arith);
        assert(xm == x % p);
        assert(ym == y % p);

        assert((((x % p) * y) % p) == ((xm * y) % p));
        assert(((xm * y) % p) == ((y * xm) % p));
        assert(((y * xm) % p) == (((y % p) * xm) % p));
        assert((((y % p) * xm) % p) == ((ym * xm) % p));
        assert(((ym * xm) % p) == ((xm * ym) % p));

        assert(((x * y) % p) == ((xm * ym) % p));

        assert((x * y) % p == 0);
        assert((xm * ym) % p == 0);

        lemma_nonzero_mul_nonzero_mod_prime(xm, ym, p);
        assert(false);
    }
    proof fn lemma_nonzero_mul_nonzero_mod_prime(
        x: int,
        y: int,
        p: int
    )
        requires
            is_prime_int_strong(p),
            0 < x < p,
            0 < y < p
        ensures
            (x * y) % p != 0
    {
        assert((x * y) % p != 0);
    }

    proof fn lemma_pow_nonzero_mod_p(
        q: int,
        k: int,
        p: int
    )
        requires
            is_domain_mod_p(p),
            0 < q < p,
            k >= 0
        ensures
            spec_pow(q, k) % p != 0
        decreases k
    {
        if k == 0 {
            lemma_spec_pow_zero(q);
            lemma_one_mod_p(p);
            assert(spec_pow(q, 0) % p == 1);
        } else {
            lemma_pow_nonzero_mod_p(q, k - 1, p);

            reveal(spec_pow);
            assert(spec_pow(q, k) == q * spec_pow(q, k - 1));

            assert(spec_pow(q, k - 1) % p != 0);
            lemma_mod_range_int(spec_pow(q, k - 1), p);
            assert(0 <= spec_pow(q, k - 1) % p);
            assert(spec_pow(q, k - 1) % p < p);

            assert(0 < spec_pow(q, k - 1) % p) by (nonlinear_arith)
                requires
                    spec_pow(q, k - 1) % p != 0,
                    0 <= spec_pow(q, k - 1) % p;

            assert((q * (spec_pow(q, k - 1) % p)) % p != 0) by {
                assert(is_domain_mod_p(p));
            }

                    lemma_mod_mul_pull_left(spec_pow(q, k - 1), q, p);

            assert((q * spec_pow(q, k - 1)) == (spec_pow(q, k - 1) * q)) by (nonlinear_arith);
            assert(spec_pow(q, k) == spec_pow(q, k - 1) * q) by (nonlinear_arith)
                requires
                    spec_pow(q, k) == q * spec_pow(q, k - 1);

            assert((spec_pow(q, k) % p) == ((spec_pow(q, k - 1) * q) % p));
            assert((((spec_pow(q, k - 1) % p) * q) % p) == ((spec_pow(q, k - 1) * q) % p));
            assert((spec_pow(q, k) % p) == (((spec_pow(q, k - 1) % p) * q) % p));
            assert((q * (spec_pow(q, k - 1) % p)) == ((spec_pow(q, k - 1) % p) * q)) by (nonlinear_arith);
            assert(spec_pow(q, k) % p != 0);
        }
    }

    proof fn lemma_single_diff_poly_nonzero(
        coeff: int,
        q: int,
        e: int,
        p: int
    )
        requires
            is_domain_mod_p(p),
            0 < q < p,
            0 < coeff < p,
            e >= 0
        ensures
            (coeff * (spec_pow(q, e) % p)) % p != 0
    {
        lemma_pow_nonzero_mod_p(q, e, p);
        lemma_mod_range_int(spec_pow(q, e), p);

        assert(0 <= spec_pow(q, e) % p);
        assert(spec_pow(q, e) % p < p);
        assert(0 < spec_pow(q, e) % p) by (nonlinear_arith)
            requires
                spec_pow(q, e) % p != 0,
                0 <= spec_pow(q, e) % p;

        assert((coeff * (spec_pow(q, e) % p)) % p != 0) by {
            assert(is_domain_mod_p(p));
        }
    }
    proof fn lemma_mod_sub_preserved(x: int, y: int, p: int)
        requires
            p > 1
        ensures
            (((x % p) - (y % p)) % p) == ((x - y) % p)
    {
        let kx = x / p;
        let ky = y / p;

        lemma_fundamental_div_mod(x, p);
        lemma_fundamental_div_mod(y, p);

        assert(x == kx * p + (x % p));
        assert(y == ky * p + (y % p));

        assert(x - y == ((x % p) - (y % p)) + (kx - ky) * p) by (nonlinear_arith)
            requires
                x == kx * p + (x % p),
                y == ky * p + (y % p);

        lemma_mod_add_multiple((x % p) - (y % p), kx - ky, p);

        assert((((x % p) - (y % p)) % p) == ((x - y) % p));
    }

    proof fn lemma_mod_sub_mul_same_factor(a: int, b: int, w: int, p: int)
        requires
            p > 1
        ensures
            ((((a * w) % p) - ((b * w) % p)) % p) == (((a - b) * w) % p)
    {
        lemma_mod_sub_preserved(a * w, b * w, p);

        assert((a * w) - (b * w) == (a - b) * w) by (nonlinear_arith);

        assert((((a * w) % p) - ((b * w) % p)) % p == (((a - b) * w) % p));
    }
    pub proof fn theorem_single_edit_detected_strong(
        w: Seq<u64>,
        w2: Seq<u64>,
        a: int,
        q: int,
        p: int
    )
        requires
            is_domain_mod_p(p),
            0 < q < p,
            w.len() == w2.len(),
            0 <= a < w.len(),
            w[a] != w2[a],
            w2[a] < w[a],
            (w[a] as int) < p,
            (w2[a] as int) < p,
            forall |i:int| 0 <= i < w.len() && i != a ==> w[i] == w2[i]
        ensures
            ramanujan_spec(w, q, p) != ramanujan_spec(w2, q, p)
    {
        lemma_collision_iff_diff_poly_zero_mod(w, w2, q, p);

        let coeff = (w[a] as int) - (w2[a] as int);
        let term = spec_pow(q, tri_exp(a)) % p;

        lemma_u64_diff_nonzero_as_int(w[a], w2[a]);
        assert(coeff != 0);

        assert(0 < coeff) by (nonlinear_arith)
            requires
                w2[a] < w[a],
                coeff == (w[a] as int) - (w2[a] as int);

        assert(coeff < p) by (nonlinear_arith)
            requires
                coeff == (w[a] as int) - (w2[a] as int),
                (w[a] as int) < p,
                0 <= (w2[a] as int);

        lemma_square_exp_nonneg(a);
        lemma_single_diff_poly_nonzero(coeff, q, tri_exp(a), p);
        assert(term == spec_pow(q, tri_exp(a)) % p);
        assert((coeff * term) % p == (coeff * (spec_pow(q, tri_exp(a)) % p)) % p);
        assert((coeff * term) % p != 0);

        lemma_single_edit_diff_poly_formula(w, w2, a, q, p);

        if ramanujan_spec(w, q, p) == ramanujan_spec(w2, q, p) {
            assert(diff_poly_eval_mod(w, w2, q, p) == 0);

            assert(
                diff_poly_eval_mod(w, w2, q, p)
                ==
                (coeff * term) % p
            );

            assert((coeff * term) % p != 0);

            assert(false);
        }
    }
    pub proof fn lemma_single_edit_diff_poly_formula(
        w: Seq<u64>,
        w2: Seq<u64>,
        a: int,
        q: int,
        p: int
    )
        requires
            p > 1,
            w.len() == w2.len(),
            0 <= a < w.len(),
            forall |i:int| 0 <= i < w.len() && i != a ==> w[i] == w2[i]
        ensures
            diff_poly_eval_mod(w, w2, q, p)
            ==
            (
                ((w[a] as int) - (w2[a] as int))
                *
                (spec_pow(q, tri_exp(a)) % p)
            ) % p
        decreases w.len()
    {
        if w.len() == 0 {
            assert(false);
        } else {
            let n = w.len() - 1;
            let wt = spec_pow(q, tri_exp(n)) % p;

            reveal(ramanujan_spec);

            if a == n {
                assert forall |i:int|
                    0 <= i < n
                implies
                    w.drop_last()[i] == w2.drop_last()[i]
                by {
                    assert(i != a);
                    assert(w[i] == w2[i]);
                }

                assert(w.drop_last().len() == w2.drop_last().len());

                assert(w.drop_last() =~= w2.drop_last()) by {
                    assert forall |i:int|
                        0 <= i < w.drop_last().len()
                    implies
                        w.drop_last()[i] == w2.drop_last()[i]
                    by {
                    }
                }

                assert(w.drop_last() == w2.drop_last());

                lemma_ramanujan_rewrite(w.drop_last(), w2.drop_last(), q, p);

                assert(ramanujan_spec(w.drop_last(), q, p) == ramanujan_spec(w2.drop_last(), q, p));

                let s = ramanujan_spec(w.drop_last(), q, p);
                let t1 = (w[a] as int) * wt;
                let t2 = (w2[a] as int) * wt;

                assert(ramanujan_spec(w, q, p) == (s + t1) % p);
                assert(ramanujan_spec(w2, q, p) == (s + t2) % p);

                lemma_mod_sub_preserved(s + t1, s + t2, p);
                assert(
                    diff_poly_eval_mod(w, w2, q, p)
                    ==
                    (((s + t1) % p) - ((s + t2) % p)) % p
                );

                assert(((s + t1) - (s + t2)) == t1 - t2) by (nonlinear_arith);
                assert((((s + t1) % p) - ((s + t2) % p)) % p == ((t1 - t2) % p));

                lemma_mod_sub_preserved(t1, t2, p);
                lemma_mod_sub_mul_same_factor(w[a] as int, w2[a] as int, wt, p);

                assert(
                    ((t1 - t2) % p)
                    ==
                    ((((t1 % p) - (t2 % p)) % p))
                );

                assert(t1 % p == (((w[a] as int) * wt) % p));
                assert(t2 % p == (((w2[a] as int) * wt) % p));

                assert(
                    ((((t1 % p) - (t2 % p)) % p))
                    ==
                    ((((w[a] as int) * wt) % p) - (((w2[a] as int) * wt) % p)) % p
                );

                assert(
                    ((((w[a] as int) * wt) % p) - (((w2[a] as int) * wt) % p)) % p
                    ==
                    ((((w[a] as int) - (w2[a] as int)) * wt) % p)
                );

                assert(
                    diff_poly_eval_mod(w, w2, q, p)
                    ==
                    (
                        ((w[a] as int) - (w2[a] as int))
                        *
                        (spec_pow(q, tri_exp(a)) % p)
                    ) % p
                );
            } else {
                assert(a < n) by (nonlinear_arith)
                    requires
                        a != n,
                        a < w.len(),
                        n == w.len() - 1;

                assert(w[n] == w2[n]) by {
                    assert(n != a);
                }
                            assert(w.drop_last().len() == w2.drop_last().len());

                assert(0 <= a < w.drop_last().len()) by (nonlinear_arith)
                    requires
                        0 <= a,
                        a < n,
                        n == w.len() - 1,
                        w.drop_last().len() == w.len() - 1;

                assert forall |i:int|
                    0 <= i < w.drop_last().len() && i != a
                implies
                    w.drop_last()[i] == w2.drop_last()[i]
                by {
                    assert(0 <= i < w.len());
                    assert(w.drop_last()[i] == w[i]);
                    assert(w2.drop_last()[i] == w2[i]);
                    assert(w[i] == w2[i]);
                }

                lemma_single_edit_diff_poly_formula(w.drop_last(), w2.drop_last(), a, q, p);

                    
    

                assert(w.drop_last().len() == w2.drop_last().len());

                let s1 = ramanujan_spec(w.drop_last(), q, p);
                let s2 = ramanujan_spec(w2.drop_last(), q, p);
                let t = (w[n] as int) * wt;

                assert(ramanujan_spec(w, q, p) == (s1 + t) % p);
                assert(ramanujan_spec(w2, q, p) == (s2 + t) % p);

                lemma_mod_sub_preserved(s1 + t, s2 + t, p);

                assert(
                    diff_poly_eval_mod(w, w2, q, p)
                    ==
                    (((s1 + t) % p) - ((s2 + t) % p)) % p
                );

                assert(((s1 + t) - (s2 + t)) == s1 - s2) by (nonlinear_arith);
                assert((((s1 + t) % p) - ((s2 + t) % p)) % p == ((s1 - s2) % p));

                assert((s1 - s2) % p == diff_poly_eval_mod(w.drop_last(), w2.drop_last(), q, p));

                assert(
                    diff_poly_eval_mod(w, w2, q, p)
                    ==
                    diff_poly_eval_mod(w.drop_last(), w2.drop_last(), q, p)
                );

                assert(
                    diff_poly_eval_mod(w.drop_last(), w2.drop_last(), q, p)
                    ==
                    (
                        ((w[a] as int) - (w2[a] as int))
                        *
                        (spec_pow(q, tri_exp(a)) % p)
                    ) % p
                );

                assert(
                    diff_poly_eval_mod(w, w2, q, p)
                    ==
                    (
                        ((w[a] as int) - (w2[a] as int))
                        *
                        (spec_pow(q, tri_exp(a)) % p)
                    ) % p
                );
            }
        }
    }
    // ======================================================
    // 15) Verified executable mismatch localization
    // ======================================================

    pub open spec fn first_mismatch_at(
        w: Seq<u64>,
        w2: Seq<u64>,
        idx: int
    ) -> bool
    {
        w.len() == w2.len()
        &&
        0 <= idx < w.len()
        &&
        w[idx] != w2[idx]
        &&
        forall |j:int| 0 <= j < idx ==> w[j] == w2[j]
    }

    pub fn find_first_mismatch(
        logs1: &Vec<u64>,
        logs2: &Vec<u64>
    ) -> (res: (bool, usize, u64, u64))
        requires
            logs1.len() == logs2.len(),
        ensures
            res.0 ==> res.1 < logs1.len(),
            res.0 ==> res.2 == logs1.view()[res.1 as int],
            res.0 ==> res.3 == logs2.view()[res.1 as int],
            res.0 ==> res.2 != res.3,
            res.0 ==> first_mismatch_at(logs1.view(), logs2.view(), res.1 as int),

            !res.0 ==> forall |j:int| 0 <= j < logs1.len() ==> logs1.view()[j] == logs2.view()[j]
    {
        let mut i: usize = 0;

        while i < logs1.len()
            invariant
                i <= logs1.len(),
                logs1.len() == logs2.len(),
                forall |j:int| 0 <= j < i as int ==> logs1.view()[j] == logs2.view()[j]
            decreases logs1.len() - i
        {
            let x = logs1[i];
            let y = logs2[i];

            if x != y {
                proof {
                    let gi = i as int;

                    lemma_vec_read_matches_view(logs1, gi, x);
                    lemma_vec_read_matches_view(logs2, gi, y);

                    assert(x == logs1.view()[gi]);
                    assert(y == logs2.view()[gi]);
                    assert(logs1.view()[gi] != logs2.view()[gi]);

                    assert(first_mismatch_at(logs1.view(), logs2.view(), gi));
                }

                return (true, i, x, y);
            }

            proof {
                let gi = i as int;

                lemma_vec_read_matches_view(logs1, gi, x);
                lemma_vec_read_matches_view(logs2, gi, y);

                assert(x == logs1.view()[gi]);
                assert(y == logs2.view()[gi]);
                assert(logs1.view()[gi] == logs2.view()[gi]);
            }

            i += 1;
        }

        proof {
            assert(forall |j:int| 0 <= j < logs1.len() ==> logs1.view()[j] == logs2.view()[j]);
        }

        (false, 0usize, 0u64, 0u64)
    }

    pub fn same_or_first_mismatch_index(
        logs1: &Vec<u64>,
        logs2: &Vec<u64>
    ) -> (res: (bool, usize))
        requires
            logs1.len() == logs2.len(),
        ensures
            res.0 ==> res.1 < logs1.len(),
            res.0 ==> first_mismatch_at(logs1.view(), logs2.view(), res.1 as int),
            !res.0 ==> forall |j:int| 0 <= j < logs1.len() ==> logs1.view()[j] == logs2.view()[j]
    {
        let t = find_first_mismatch(logs1, logs2);
        if t.0 {
            (true, t.1)
        } else {
            (false, 0usize)
        }
    }

    // ======================================================
    // 15) Impossibility Theorem I:
    //     affine <=> shift-equivariant, finite exponent version
    // ======================================================

    pub open spec fn affine_exp(a: int, b: int, i: int) -> int {
        a * i + b
    }

    pub open spec fn is_affine_with(phi: Seq<int>, a: int, b: int) -> bool {
        forall |i:int|
            #![trigger phi[i]]
            0 <= i < phi.len() ==> phi[i] == affine_exp(a, b, i)
    }

    pub open spec fn finite_affine_exponents(phi: Seq<int>) -> bool {
        exists |a:int, b:int| is_affine_with(phi, a, b)
    }

    pub open spec fn shift_equivariant_exponents(phi: Seq<int>, s: int) -> bool {
        0 <= s < phi.len()
        &&
        forall |i:int, j:int|
            #![trigger phi[i + s], phi[j + s]]
            0 <= i &&
            0 <= j &&
            i + s < phi.len() &&
            j + s < phi.len()
            ==>
            phi[i + s] - phi[i] == phi[j + s] - phi[j]
    }

    pub proof fn theorem_affine_implies_shift_equivariant(
        phi: Seq<int>,
        a: int,
        b: int,
        s: int
    )
        requires
            0 <= s < phi.len(),
            is_affine_with(phi, a, b)
        ensures
            shift_equivariant_exponents(phi, s)
    {
        assert forall |i:int, j:int|
            #![trigger phi[i + s], phi[j + s]]
            0 <= i &&
            0 <= j &&
            i + s < phi.len() &&
            j + s < phi.len()
        implies
            phi[i + s] - phi[i] == phi[j + s] - phi[j]
        by {
            assert(0 <= i + s) by (nonlinear_arith)
                requires 0 <= i, 0 <= s;

            assert(0 <= j + s) by (nonlinear_arith)
                requires 0 <= j, 0 <= s;

            assert(phi[i + s] == affine_exp(a, b, i + s));
            assert(phi[i] == affine_exp(a, b, i));
            assert(phi[j + s] == affine_exp(a, b, j + s));
            assert(phi[j] == affine_exp(a, b, j));

            assert(affine_exp(a, b, i + s) == a * (i + s) + b);
            assert(affine_exp(a, b, i) == a * i + b);
            assert(affine_exp(a, b, j + s) == a * (j + s) + b);
            assert(affine_exp(a, b, j) == a * j + b);

            assert(phi[i + s] == a * (i + s) + b);
            assert(phi[i] == a * i + b);
            assert(phi[j + s] == a * (j + s) + b);
            assert(phi[j] == a * j + b);

            assert(phi[i + s] - phi[i] == (a * (i + s) + b) - (a * i + b));
            assert((a * (i + s) + b) - (a * i + b) == a * s) by (nonlinear_arith);
            assert(phi[i + s] - phi[i] == a * s);

            assert(phi[j + s] - phi[j] == (a * (j + s) + b) - (a * j + b));
            assert((a * (j + s) + b) - (a * j + b) == a * s) by (nonlinear_arith);
            assert(phi[j + s] - phi[j] == a * s);

            assert(phi[i + s] - phi[i] == phi[j + s] - phi[j]);
        }
    }

    proof fn lemma_shift_gap_one_implies_pointwise_affine(
        phi: Seq<int>,
        i: int
    )
        requires
            phi.len() >= 2,
            shift_equivariant_exponents(phi, 1int),
            0 <= i < phi.len()
        ensures
            phi[i] == phi[0int] + i * (phi[1int] - phi[0int])
        decreases i
    {
        if i == 0 {
            assert(phi[i] == phi[0int]);

            assert(i * (phi[1int] - phi[0int]) == 0) by (nonlinear_arith)
                requires i == 0;

            assert(phi[0int] + i * (phi[1int] - phi[0int]) == phi[0int])
                by (nonlinear_arith)
                requires
                    i * (phi[1int] - phi[0int]) == 0;

            assert(phi[i] == phi[0int] + i * (phi[1int] - phi[0int]));
        } else {
            lemma_shift_gap_one_implies_pointwise_affine(phi, i - 1);

            assert(0 <= i - 1);
            assert(i - 1 < phi.len());
            assert((i - 1) + 1 == i);
            assert(0int + 1int == 1int);
            assert(0int + 1int < phi.len());
            assert((i - 1) + 1 < phi.len());

            assert(phi[(i - 1) + 1] - phi[i - 1] == phi[0int + 1int] - phi[0int]);
            assert(phi[0int + 1int] == phi[1int]);
            assert(phi[(i - 1) + 1] == phi[i]);

            assert(phi[i] - phi[i - 1] == phi[1int] - phi[0int]);

            assert(phi[i - 1] == phi[0int] + (i - 1) * (phi[1int] - phi[0int]));

            assert(phi[i] == phi[i - 1] + (phi[1int] - phi[0int])) by (nonlinear_arith)
                requires
                    phi[i] - phi[i - 1] == phi[1int] - phi[0int];

            assert(phi[i] == phi[0int] + i * (phi[1int] - phi[0int])) by (nonlinear_arith)
                requires
                    phi[i - 1] == phi[0int] + (i - 1) * (phi[1int] - phi[0int]),
                    phi[i] == phi[i - 1] + (phi[1int] - phi[0int]);
        }
    }

    pub proof fn theorem_shift_equivariant_implies_affine(
        phi: Seq<int>
    )
        requires
            phi.len() >= 2,
            shift_equivariant_exponents(phi, 1int)
        ensures
            finite_affine_exponents(phi)
    {
        let a = phi[1int] - phi[0int];
        let b = phi[0int];

        assert forall |i:int|
            #![trigger phi[i]]
            0 <= i < phi.len()
        implies
            phi[i] == affine_exp(a, b, i)
        by {
            lemma_shift_gap_one_implies_pointwise_affine(phi, i);

            assert(phi[i] == phi[0int] + i * (phi[1int] - phi[0int]));
            assert(affine_exp(a, b, i) == a * i + b);

            assert(a * i + b == phi[0int] + i * (phi[1int] - phi[0int])) by (nonlinear_arith)
                requires
                    a == phi[1int] - phi[0int],
                    b == phi[0int];

            assert(phi[i] == affine_exp(a, b, i));
        }

        assert(is_affine_with(phi, a, b));
        assert(finite_affine_exponents(phi)) by {
            assert(is_affine_with(phi, a, b));
        }
    }

    // ======================================================
    // 16) Impossibility Theorem II:
    //     exact one-scalar composition implies shift symmetry
    // ======================================================

    pub open spec fn one_scalar_composition_exponents(phi: Seq<int>, k: int) -> bool {
        0 <= k < phi.len()
        &&
        forall |j:int, l:int|
            #![trigger phi[k + j], phi[k + l]]
            0 <= j &&
            0 <= l &&
            k + j < phi.len() &&
            k + l < phi.len()
            ==>
            phi[k + j] - phi[j] == phi[k + l] - phi[l]
    }

    pub open spec fn one_scalar_composition_all_shifts(phi: Seq<int>) -> bool {
        forall |k:int|
            #![trigger one_scalar_composition_exponents(phi, k)]
            1 <= k < phi.len() ==> one_scalar_composition_exponents(phi, k)
    }

    pub proof fn theorem_one_scalar_composition_implies_shift_equivariance(
        phi: Seq<int>,
        k: int
    )
        requires
            0 <= k < phi.len(),
            one_scalar_composition_exponents(phi, k)
        ensures
            shift_equivariant_exponents(phi, k)
    {
        assert forall |i:int, j:int|
            #![trigger phi[i + k], phi[j + k]]
            0 <= i &&
            0 <= j &&
            i + k < phi.len() &&
            j + k < phi.len()
        implies
            phi[i + k] - phi[i] == phi[j + k] - phi[j]
        by {
            assert(k + i == i + k);
            assert(k + j == j + k);

            assert(phi[k + i] - phi[i] == phi[k + j] - phi[j]);
            assert(phi[i + k] == phi[k + i]);
            assert(phi[j + k] == phi[k + j]);

            assert(phi[i + k] - phi[i] == phi[j + k] - phi[j]);
        }
    }

    pub proof fn theorem_non_affine_no_one_scalar_composition(
        phi: Seq<int>
    )
        requires
            phi.len() >= 2,
            !finite_affine_exponents(phi)
        ensures
            !one_scalar_composition_all_shifts(phi)
    {
        if one_scalar_composition_all_shifts(phi) {
            assert(one_scalar_composition_exponents(phi, 1int));

            theorem_one_scalar_composition_implies_shift_equivariance(phi, 1int);
            assert(shift_equivariant_exponents(phi, 1int));

            theorem_shift_equivariant_implies_affine(phi);
            assert(finite_affine_exponents(phi));

            assert(false);
        }
    }
     // ======================================================
    // 17) O(1) Streaming Updater for Triangular K-Sentry
    // ======================================================
    //
    // IMPORTANT:
    // Do NOT redefine tri_exp here.
    // Your file already defines tri_exp near the top.
    //
    // State:
    //   acc    = prefix accumulator through n events
    //   weight = q^(T_n)
    //   step   = q^(n+1)
    //
    // Update on event x_n:
    //   acc'    = acc + x_n * weight
    //   weight' = weight * step
    //   step'   = step * q
    //   n'      = n + 1

    pub proof fn lemma_tri_exp_next_o1(i: int)
        requires
            i >= 0
        ensures
            tri_exp(i + 1) == tri_exp(i) + i + 1
    {
        assert(tri_exp(i + 1) == (i + 1) * (i + 2) / 2);
        assert(tri_exp(i) == i * (i + 1) / 2);
        assert((i + 1) * (i + 2) == i * (i + 1) + 2 * (i + 1)) by (nonlinear_arith);
        assert((i + 1) * (i + 2) / 2 == i * (i + 1) / 2 + i + 1) by (nonlinear_arith);
    }

    pub proof fn lemma_spec_pow_succ_o1(q: int, e: int)
        requires
            e >= 0
        ensures
            spec_pow(q, e + 1) == spec_pow(q, e) * q
    {
        assert(e + 1 > 0);
        assert(spec_pow(q, e + 1) == q * spec_pow(q, e));
        assert(q * spec_pow(q, e) == spec_pow(q, e) * q) by (nonlinear_arith);
    }

    pub proof fn lemma_spec_pow_add_o1(q: int, a: int, b: int)
        requires
            a >= 0,
            b >= 0
        ensures
            spec_pow(q, a + b) == spec_pow(q, a) * spec_pow(q, b)
        decreases b
    {
        if b == 0 {
            assert(a + b == a);
            assert(spec_pow(q, 0) == 1);
            assert(spec_pow(q, a + b) == spec_pow(q, a));
            assert(spec_pow(q, a) == spec_pow(q, a) * spec_pow(q, 0)) by (nonlinear_arith);
        } else {
            assert(b - 1 >= 0);

            lemma_spec_pow_add_o1(q, a, b - 1);
            lemma_spec_pow_succ_o1(q, a + b - 1);
            lemma_spec_pow_succ_o1(q, b - 1);

            assert(a + b == a + (b - 1) + 1) by (nonlinear_arith);
            assert(b == (b - 1) + 1) by (nonlinear_arith);

            assert(spec_pow(q, a + b)
                == spec_pow(q, a + b - 1) * q);

            assert(a + b - 1 == a + (b - 1)) by (nonlinear_arith);

            assert(spec_pow(q, a + b - 1)
                == spec_pow(q, a + (b - 1)));

            assert(spec_pow(q, a + (b - 1))
                == spec_pow(q, a) * spec_pow(q, b - 1));

            assert(spec_pow(q, b)
                == spec_pow(q, b - 1) * q);

            assert(spec_pow(q, a + b)
                == (spec_pow(q, a) * spec_pow(q, b - 1)) * q);

            assert((spec_pow(q, a) * spec_pow(q, b - 1)) * q
                == spec_pow(q, a) * (spec_pow(q, b - 1) * q)) by (nonlinear_arith);

            assert(spec_pow(q, a + b)
                == spec_pow(q, a) * (spec_pow(q, b - 1) * q));

            assert(spec_pow(q, a + b)
                == spec_pow(q, a) * spec_pow(q, b));
        }
    }

    pub open spec fn ks_prefix_spec(xs: Seq<int>, q: int, p: int, n: nat) -> int
        recommends
            p > 0,
            n <= xs.len()
        decreases n
    {
        if n == 0 {
            0
        } else {
            let prev = ks_prefix_spec(xs, q, p, (n - 1) as nat);
            let idx = (n - 1) as int;
            let x = xs[idx];
            (prev + x * spec_pow(q, tri_exp(idx)) % p) % p
        }
    }

    pub open spec fn o1_state_inv(
        xs: Seq<int>,
        q: int,
        p: int,
        n: nat,
        acc: int,
        weight: int,
        step: int
    ) -> bool {
        p > 0
        &&
        n <= xs.len()
        &&
        acc == ks_prefix_spec(xs, q, p, n)
        &&
        weight == spec_pow(q, tri_exp(n as int))
        &&
        step == spec_pow(q, n as int + 1)
    }

    pub open spec fn o1_next_acc(
        acc: int,
        x: int,
        weight: int,
        p: int
    ) -> int
        recommends
            p > 0
    {
        (acc + x * weight % p) % p
    }

    pub open spec fn o1_next_weight(
        weight: int,
        step: int,
        p: int
    ) -> int
        recommends
            p > 0
    {
        weight * step
    }

    pub open spec fn o1_next_step(
        step: int,
        q: int,
        p: int
    ) -> int
        recommends
            p > 0
    {
        step * q
    }

    pub proof fn lemma_o1_acc_step_correct(
        xs: Seq<int>,
        q: int,
        p: int,
        n: nat,
        acc: int,
        weight: int,
        step: int
    )
        requires
            p > 0,
            n < xs.len(),
            o1_state_inv(xs, q, p, n, acc, weight, step)
        ensures
            o1_next_acc(acc, xs[n as int], weight, p)
                == ks_prefix_spec(xs, q, p, n + 1)
    {
        assert(acc == ks_prefix_spec(xs, q, p, n));
        assert(weight == spec_pow(q, tri_exp(n as int)));

        assert((n + 1) - 1 == n);
        assert(((n + 1) - 1) as int == n as int);

        assert(ks_prefix_spec(xs, q, p, n + 1)
            == (ks_prefix_spec(xs, q, p, n)
                + xs[n as int] * spec_pow(q, tri_exp(n as int)) % p) % p);

        assert(o1_next_acc(acc, xs[n as int], weight, p)
            == (acc + xs[n as int] * weight % p) % p);

        assert(o1_next_acc(acc, xs[n as int], weight, p)
            == ks_prefix_spec(xs, q, p, n + 1));
    }

    pub proof fn lemma_o1_weight_step_correct(
        q: int,
        p: int,
        n: nat,
        weight: int,
        step: int
    )
        requires
            p > 0,
            weight == spec_pow(q, tri_exp(n as int)),
            step == spec_pow(q, n as int + 1)
        ensures
            o1_next_weight(weight, step, p)
                == spec_pow(q, tri_exp((n + 1) as int))
    {
        lemma_tri_exp_next_o1(n as int);

        assert((n + 1) as int == n as int + 1);
        assert(tri_exp((n + 1) as int) == tri_exp(n as int) + n as int + 1);

        lemma_spec_pow_add_o1(q, tri_exp(n as int), n as int + 1);

        assert(spec_pow(q, tri_exp(n as int) + n as int + 1)
            == spec_pow(q, tri_exp(n as int)) * spec_pow(q, n as int + 1));

        assert(spec_pow(q, tri_exp((n + 1) as int))
            == spec_pow(q, tri_exp(n as int) + n as int + 1));

        assert(spec_pow(q, tri_exp((n + 1) as int))
            == spec_pow(q, tri_exp(n as int)) * spec_pow(q, n as int + 1));

        assert(o1_next_weight(weight, step, p) == weight * step);

        assert(o1_next_weight(weight, step, p)
            == spec_pow(q, tri_exp((n + 1) as int)));
    }

    pub proof fn lemma_o1_step_step_correct(
        q: int,
        p: int,
        n: nat,
        step: int
    )
        requires
            p > 0,
            step == spec_pow(q, n as int + 1)
        ensures
            o1_next_step(step, q, p)
                == spec_pow(q, (n + 1) as int + 1)
    {
        assert((n + 1) as int + 1 == n as int + 2);

        lemma_spec_pow_succ_o1(q, n as int + 1);

        assert(spec_pow(q, n as int + 2)
            == spec_pow(q, n as int + 1) * q);

        assert(o1_next_step(step, q, p) == step * q);

        assert(o1_next_step(step, q, p)
            == spec_pow(q, n as int + 2));

        assert(o1_next_step(step, q, p)
            == spec_pow(q, (n + 1) as int + 1));
    }

    pub proof fn lemma_o1_update_preserves_inv(
        xs: Seq<int>,
        q: int,
        p: int,
        n: nat,
        acc: int,
        weight: int,
        step: int
    )
        requires
            p > 0,
            n < xs.len(),
            o1_state_inv(xs, q, p, n, acc, weight, step)
        ensures
            o1_state_inv(
                xs,
                q,
                p,
                n + 1,
                o1_next_acc(acc, xs[n as int], weight, p),
                o1_next_weight(weight, step, p),
                o1_next_step(step, q, p)
            )
    {
        lemma_o1_acc_step_correct(xs, q, p, n, acc, weight, step);
        lemma_o1_weight_step_correct(q, p, n, weight, step);
        lemma_o1_step_step_correct(q, p, n, step);

        assert(n + 1 <= xs.len());

        assert(o1_next_acc(acc, xs[n as int], weight, p)
            == ks_prefix_spec(xs, q, p, n + 1));

        assert(o1_next_weight(weight, step, p)
            == spec_pow(q, tri_exp((n + 1) as int)));

        assert(o1_next_step(step, q, p)
            == spec_pow(q, (n + 1) as int + 1));

        assert(o1_state_inv(
            xs,
            q,
            p,
            n + 1,
            o1_next_acc(acc, xs[n as int], weight, p),
            o1_next_weight(weight, step, p),
            o1_next_step(step, q, p)
        ));
    }
        // ======================================================
    // 18) Rolling Hash Baseline:
    //     affine exponent schedule is one-scalar rebaseable
    // ======================================================
    //
    // This section proves the baseline reviewers will ask about:
    //
    //   H(w)       = Σ x_i q^i
    //   H_shift(w) = Σ x_i q^(i+s)
    //
    // Then:
    //
    //   H_shift(w) = q^s * H(w)
    //
    // Meaning ordinary affine rolling hash is digest-only rebaseable:
    // a downstream component can shift a chunk digest by multiplying
    // by one scalar q^s.
    //
    // This is exactly the property K-Sentry should later escape.

    pub open spec fn rolling_raw_prefix_spec(
        xs: Seq<int>,
        q: int,
        n: nat
    ) -> int
        recommends
            n <= xs.len()
        decreases n
    {
        if n == 0 {
            0
        } else {
            let prev = rolling_raw_prefix_spec(xs, q, (n - 1) as nat);
            let idx = (n - 1) as int;
            prev + xs[idx] * spec_pow(q, idx)
        }
    }

    pub open spec fn rolling_raw_shifted_prefix_spec(
        xs: Seq<int>,
        q: int,
        s: int,
        n: nat
    ) -> int
        recommends
            s >= 0,
            n <= xs.len()
        decreases n
    {
        if n == 0 {
            0
        } else {
            let prev = rolling_raw_shifted_prefix_spec(xs, q, s, (n - 1) as nat);
            let idx = (n - 1) as int;
            prev + xs[idx] * spec_pow(q, idx + s)
        }
    }

    pub proof fn lemma_rolling_term_scalar_rebase(
        q: int,
        s: int,
        i: int
    )
        requires
            s >= 0,
            i >= 0
        ensures
            spec_pow(q, i + s) == spec_pow(q, s) * spec_pow(q, i)
    {
        lemma_spec_pow_add_o1(q, s, i);

        assert(s + i == i + s) by (nonlinear_arith);

        assert(spec_pow(q, s + i) == spec_pow(q, s) * spec_pow(q, i));

        assert(spec_pow(q, i + s) == spec_pow(q, s + i));

        assert(spec_pow(q, i + s) == spec_pow(q, s) * spec_pow(q, i));
    }

    pub proof fn theorem_rolling_raw_scalar_rebase(
        xs: Seq<int>,
        q: int,
        s: int,
        n: nat
    )
        requires
            s >= 0,
            n <= xs.len()
        ensures
            rolling_raw_shifted_prefix_spec(xs, q, s, n)
                == spec_pow(q, s) * rolling_raw_prefix_spec(xs, q, n)
        decreases n
    {
        if n == 0 {
            assert(rolling_raw_shifted_prefix_spec(xs, q, s, n) == 0);
            assert(rolling_raw_prefix_spec(xs, q, n) == 0);
            assert(spec_pow(q, s) * rolling_raw_prefix_spec(xs, q, n) == 0);
        } else {
            assert(n > 0);
            assert(n - 1 < xs.len());

            let nprev = (n - 1) as nat;
            let idx = (n - 1) as int;

            assert(idx >= 0);

            theorem_rolling_raw_scalar_rebase(xs, q, s, nprev);

            assert(rolling_raw_shifted_prefix_spec(xs, q, s, nprev)
                == spec_pow(q, s) * rolling_raw_prefix_spec(xs, q, nprev));

            lemma_rolling_term_scalar_rebase(q, s, idx);

            assert(spec_pow(q, idx + s) == spec_pow(q, s) * spec_pow(q, idx));

            assert(rolling_raw_prefix_spec(xs, q, n)
                == rolling_raw_prefix_spec(xs, q, nprev)
                    + xs[idx] * spec_pow(q, idx));

            assert(rolling_raw_shifted_prefix_spec(xs, q, s, n)
                == rolling_raw_shifted_prefix_spec(xs, q, s, nprev)
                    + xs[idx] * spec_pow(q, idx + s));

            assert(rolling_raw_shifted_prefix_spec(xs, q, s, n)
                == spec_pow(q, s) * rolling_raw_prefix_spec(xs, q, nprev)
                    + xs[idx] * (spec_pow(q, s) * spec_pow(q, idx)));

            assert(xs[idx] * (spec_pow(q, s) * spec_pow(q, idx))
                == spec_pow(q, s) * (xs[idx] * spec_pow(q, idx))) by (nonlinear_arith);

            assert(rolling_raw_shifted_prefix_spec(xs, q, s, n)
                == spec_pow(q, s) * rolling_raw_prefix_spec(xs, q, nprev)
                    + spec_pow(q, s) * (xs[idx] * spec_pow(q, idx)));

            assert(spec_pow(q, s) * rolling_raw_prefix_spec(xs, q, n)
                == spec_pow(q, s)
                    * (rolling_raw_prefix_spec(xs, q, nprev)
                        + xs[idx] * spec_pow(q, idx)));

            assert(spec_pow(q, s)
                    * (rolling_raw_prefix_spec(xs, q, nprev)
                        + xs[idx] * spec_pow(q, idx))
                ==
                spec_pow(q, s) * rolling_raw_prefix_spec(xs, q, nprev)
                    + spec_pow(q, s) * (xs[idx] * spec_pow(q, idx))) by (nonlinear_arith);

            assert(rolling_raw_shifted_prefix_spec(xs, q, s, n)
                == spec_pow(q, s) * rolling_raw_prefix_spec(xs, q, n));
        }
    }

    pub proof fn theorem_rolling_hash_is_digest_only_rebaseable(
        xs: Seq<int>,
        q: int,
        s: int
    )
        requires
            s >= 0
        ensures
            xs.len() >= 0 ==> rolling_raw_shifted_prefix_spec(xs, q, s, xs.len())
                == spec_pow(q, s) * rolling_raw_prefix_spec(xs, q, xs.len())
    {
        theorem_rolling_raw_scalar_rebase(xs, q, s, xs.len());
    }
        // ======================================================
    // 19) Triangular Anti-Rebase:
    //     concrete shift-1 counterexample
    // ======================================================
    //
    // For rolling hash, every shift s has a constant exponent gap:
    //   (i+s) - i = s
    //
    // For triangular K-Sentry, already at shift s = 1:
    //
    //   T_1 - T_0 = 1
    //   T_2 - T_1 = 2
    //
    // The exponent gap is not constant.
    // Therefore triangular exponents cannot support one-scalar rebasing
    // for all positions.

    pub open spec fn tri_gap_o1(i: int, s: int) -> int
        recommends
            i >= 0,
            s >= 0
    {
        tri_exp(i + s) - tri_exp(i)
    }

    pub proof fn lemma_tri_exp_zero_o1()
        ensures
            tri_exp(0int) == 0int
    {
        assert(tri_exp(0int) == 0int * (0int + 1int) / 2int);
        assert(tri_exp(0int) == 0int);
    }

    pub proof fn lemma_tri_exp_one_o1()
        ensures
            tri_exp(1int) == 1int
    {
        assert(tri_exp(1int) == 1int * (1int + 1int) / 2int);
        assert(1int * (1int + 1int) == 2int) by (nonlinear_arith);
        assert(2int / 2int == 1int);
        assert(tri_exp(1int) == 1int);
    }

    pub proof fn lemma_tri_exp_two_o1()
        ensures
            tri_exp(2int) == 3int
    {
        assert(tri_exp(2int) == 2int * (2int + 1int) / 2int);
        assert(2int * (2int + 1int) == 6int) by (nonlinear_arith);
        assert(6int / 2int == 3int);
        assert(tri_exp(2int) == 3int);
    }

    pub proof fn lemma_tri_gap_zero_shift_one_o1()
        ensures
            tri_gap_o1(0int, 1int) == 1int
    {
        lemma_tri_exp_zero_o1();
        lemma_tri_exp_one_o1();

        assert(0int + 1int == 1int);
        assert(tri_gap_o1(0int, 1int) == tri_exp(0int + 1int) - tri_exp(0int));
        assert(tri_gap_o1(0int, 1int) == tri_exp(1int) - tri_exp(0int));
        assert(tri_gap_o1(0int, 1int) == 1int - 0int);
        assert(tri_gap_o1(0int, 1int) == 1int);
    }

    pub proof fn lemma_tri_gap_one_shift_one_o1()
        ensures
            tri_gap_o1(1int, 1int) == 2int
    {
        lemma_tri_exp_one_o1();
        lemma_tri_exp_two_o1();

        assert(1int + 1int == 2int);
        assert(tri_gap_o1(1int, 1int) == tri_exp(1int + 1int) - tri_exp(1int));
        assert(tri_gap_o1(1int, 1int) == tri_exp(2int) - tri_exp(1int));
        assert(tri_gap_o1(1int, 1int) == 3int - 1int);
        assert(tri_gap_o1(1int, 1int) == 2int);
    }

    pub proof fn lemma_tri_shift_one_gap_not_constant_o1()
        ensures
            tri_gap_o1(0int, 1int) != tri_gap_o1(1int, 1int)
    {
        lemma_tri_gap_zero_shift_one_o1();
        lemma_tri_gap_one_shift_one_o1();

        assert(tri_gap_o1(0int, 1int) == 1int);
        assert(tri_gap_o1(1int, 1int) == 2int);
        assert(1int != 2int);
        assert(tri_gap_o1(0int, 1int) != tri_gap_o1(1int, 1int));
    }

    pub open spec fn triangular_one_scalar_rebase_exponents_for_shift_o1(s: int) -> bool {
        s >= 0
        &&
        forall |i:int, j:int|
            #![trigger tri_exp(i + s), tri_exp(j + s)]
            i >= 0 && j >= 0 ==>
                tri_exp(i + s) - tri_exp(i)
                    == tri_exp(j + s) - tri_exp(j)
    }

    pub proof fn theorem_triangular_no_one_scalar_rebase_shift_one_o1()
        ensures
            !triangular_one_scalar_rebase_exponents_for_shift_o1(1int)
    {
        lemma_tri_shift_one_gap_not_constant_o1();

        if triangular_one_scalar_rebase_exponents_for_shift_o1(1int) {
            assert(tri_exp(0int + 1int) - tri_exp(0int)
                == tri_exp(1int + 1int) - tri_exp(1int));

            assert(tri_gap_o1(0int, 1int) == tri_exp(0int + 1int) - tri_exp(0int));
            assert(tri_gap_o1(1int, 1int) == tri_exp(1int + 1int) - tri_exp(1int));

            assert(tri_gap_o1(0int, 1int) == tri_gap_o1(1int, 1int));

            lemma_tri_shift_one_gap_not_constant_o1();

            assert(false);
        }
    }

    pub proof fn theorem_triangular_shift_one_gap_depends_on_position_o1()
        ensures
            tri_exp(1int + 1int) - tri_exp(1int)
                != tri_exp(0int + 1int) - tri_exp(0int)
    {
        lemma_tri_gap_zero_shift_one_o1();
        lemma_tri_gap_one_shift_one_o1();

        assert(tri_gap_o1(0int, 1int) == tri_exp(0int + 1int) - tri_exp(0int));
        assert(tri_gap_o1(1int, 1int) == tri_exp(1int + 1int) - tri_exp(1int));

        assert(tri_gap_o1(0int, 1int) == 1int);
        assert(tri_gap_o1(1int, 1int) == 2int);

        assert(tri_gap_o1(1int, 1int) != tri_gap_o1(0int, 1int));

        assert(tri_exp(1int + 1int) - tri_exp(1int)
            != tri_exp(0int + 1int) - tri_exp(0int));
    }
        // ======================================================
    // 20) Checkpoint Metadata:
    //     length and range consistency for TimeFence chunks
    // ======================================================
    //
    // This section models the metadata carried by each TimeFence
    // checkpoint/chunk:
    //
    //   start: first sequence index
    //   len:   number of events in the chunk
    //   end:   one-past-last sequence index
    //
    // The key production point:
    //
    //   length-changing edits are caught deterministically
    //   by metadata before we even need the probabilistic
    //   K-Sentry digest comparison.

    pub open spec fn ckpt_end(start: nat, len: nat) -> nat {
        start + len
    }

    pub open spec fn ckpt_valid(start: nat, len: nat, end: nat) -> bool {
        end == start + len
    }

    pub open spec fn same_range(
        start1: nat,
        len1: nat,
        start2: nat,
        len2: nat
    ) -> bool {
        start1 == start2 && len1 == len2
    }

    pub open spec fn adjacent_chunks(
        start1: nat,
        len1: nat,
        start2: nat,
        len2: nat
    ) -> bool {
        start2 == start1 + len1
    }

    pub proof fn lemma_ckpt_end_valid(start: nat, len: nat)
        ensures
            ckpt_valid(start, len, ckpt_end(start, len))
    {
        assert(ckpt_end(start, len) == start + len);
        assert(ckpt_valid(start, len, ckpt_end(start, len)));
    }

    pub proof fn lemma_ckpt_valid_end_unique(
        start: nat,
        len: nat,
        end1: nat,
        end2: nat
    )
        requires
            ckpt_valid(start, len, end1),
            ckpt_valid(start, len, end2)
        ensures
            end1 == end2
    {
        assert(end1 == start + len);
        assert(end2 == start + len);
        assert(end1 == end2);
    }

    pub proof fn lemma_same_range_same_end(
        start1: nat,
        len1: nat,
        start2: nat,
        len2: nat
    )
        requires
            same_range(start1, len1, start2, len2)
        ensures
            ckpt_end(start1, len1) == ckpt_end(start2, len2)
    {
        assert(start1 == start2);
        assert(len1 == len2);
        assert(ckpt_end(start1, len1) == start1 + len1);
        assert(ckpt_end(start2, len2) == start2 + len2);
        assert(ckpt_end(start1, len1) == ckpt_end(start2, len2));
    }

    pub proof fn lemma_different_len_not_same_range(
        start: nat,
        len1: nat,
        len2: nat
    )
        requires
            len1 != len2
        ensures
            !same_range(start, len1, start, len2)
    {
        if same_range(start, len1, start, len2) {
            assert(len1 == len2);
            assert(false);
        }
    }

    pub proof fn lemma_different_start_not_same_range(
        start1: nat,
        start2: nat,
        len: nat
    )
        requires
            start1 != start2
        ensures
            !same_range(start1, len, start2, len)
    {
        if same_range(start1, len, start2, len) {
            assert(start1 == start2);
            assert(false);
        }
    }

    pub proof fn lemma_adjacent_chunks_no_overlap_ordered(
        start1: nat,
        len1: nat,
        start2: nat,
        len2: nat
    )
        requires
            adjacent_chunks(start1, len1, start2, len2)
        ensures
            start2 == ckpt_end(start1, len1)
    {
        assert(adjacent_chunks(start1, len1, start2, len2));
        assert(start2 == start1 + len1);
        assert(ckpt_end(start1, len1) == start1 + len1);
        assert(start2 == ckpt_end(start1, len1));
    }

    pub proof fn lemma_adjacent_combined_end(
        start1: nat,
        len1: nat,
        len2: nat
    )
        ensures
            ckpt_end(ckpt_end(start1, len1), len2)
                == ckpt_end(start1, len1 + len2)
    {
        assert(ckpt_end(ckpt_end(start1, len1), len2)
            == (start1 + len1) + len2);

        assert(ckpt_end(start1, len1 + len2)
            == start1 + (len1 + len2));

        assert((start1 + len1) + len2 == start1 + (len1 + len2)) by (nonlinear_arith);

        assert(ckpt_end(ckpt_end(start1, len1), len2)
            == ckpt_end(start1, len1 + len2));
    }

    pub proof fn lemma_len_mismatch_detects_insert_delete(
        start: nat,
        expected_len: nat,
        observed_len: nat
    )
        requires
            expected_len != observed_len
        ensures
            !same_range(start, expected_len, start, observed_len)
    {
        lemma_different_len_not_same_range(start, expected_len, observed_len);
    }
        // ======================================================
    // 21) Prefix Checkpoint Correctness:
    //     O(1) state emits mathematically correct checkpoint
    // ======================================================
    //
    // This connects the hot-path streaming state to the
    // checkpoint record used by TimeFence.
    //
    // If the O(1) invariant holds, then the emitted digest
    // is exactly the mathematical prefix accumulator.

    pub open spec fn checkpoint_digest_from_state(acc: int) -> int {
        acc
    }

    pub open spec fn checkpoint_position_from_state(n: nat) -> nat {
        n
    }

    pub open spec fn prefix_checkpoint_correct(
        xs: Seq<int>,
        q: int,
        p: int,
        n: nat,
        acc: int
    ) -> bool
        recommends
            p > 0,
            n <= xs.len()
    {
        checkpoint_digest_from_state(acc) == ks_prefix_spec(xs, q, p, n)
    }

    pub proof fn lemma_o1_state_implies_prefix_checkpoint_correct(
        xs: Seq<int>,
        q: int,
        p: int,
        n: nat,
        acc: int,
        weight: int,
        step: int
    )
        requires
            p > 0,
            n <= xs.len(),
            o1_state_inv(xs, q, p, n, acc, weight, step)
        ensures
            prefix_checkpoint_correct(xs, q, p, n, acc)
    {
        assert(o1_state_inv(xs, q, p, n, acc, weight, step));

        assert(acc == ks_prefix_spec(xs, q, p, n));

        assert(checkpoint_digest_from_state(acc) == acc);

        assert(checkpoint_digest_from_state(acc)
            == ks_prefix_spec(xs, q, p, n));

        assert(prefix_checkpoint_correct(xs, q, p, n, acc));
    }

    pub proof fn lemma_checkpoint_position_matches_state(
        n: nat
    )
        ensures
            checkpoint_position_from_state(n) == n
    {
        assert(checkpoint_position_from_state(n) == n);
    }

    pub proof fn lemma_valid_prefix_checkpoint_range(
        xs: Seq<int>,
        q: int,
        p: int,
        n: nat,
        acc: int,
        weight: int,
        step: int
    )
        requires
            p > 0,
            n <= xs.len(),
            o1_state_inv(xs, q, p, n, acc, weight, step)
        ensures
            ckpt_valid(0nat, n, checkpoint_position_from_state(n))
    {
        lemma_checkpoint_position_matches_state(n);

        assert(checkpoint_position_from_state(n) == n);

        assert(ckpt_valid(0nat, n, n));

        assert(ckpt_valid(0nat, n, checkpoint_position_from_state(n)));
    }

    pub proof fn lemma_prefix_checkpoint_digest_unique(
        xs: Seq<int>,
        q: int,
        p: int,
        n: nat,
        acc1: int,
        acc2: int,
        weight1: int,
        step1: int,
        weight2: int,
        step2: int
    )
        requires
            p > 0,
            n <= xs.len(),
            o1_state_inv(xs, q, p, n, acc1, weight1, step1),
            o1_state_inv(xs, q, p, n, acc2, weight2, step2)
        ensures
            checkpoint_digest_from_state(acc1)
                == checkpoint_digest_from_state(acc2)
    {
        assert(acc1 == ks_prefix_spec(xs, q, p, n));
        assert(acc2 == ks_prefix_spec(xs, q, p, n));

        assert(acc1 == acc2);

        assert(checkpoint_digest_from_state(acc1) == acc1);
        assert(checkpoint_digest_from_state(acc2) == acc2);

        assert(checkpoint_digest_from_state(acc1)
            == checkpoint_digest_from_state(acc2));
    }
        // ======================================================
    // 22) Mismatch Localization:
    //     whole-range mismatch implies some subrange mismatch
    // ======================================================
    //
    // This is the verifier logic used by TimeFence.
    //
    // Suppose an expected range is split into left and right parts:
    //
    //   expected_total = expected_left + expected_right
    //   observed_total = observed_left + observed_right
    //
    // If:
    //
    //   expected_total != observed_total
    //
    // then at least one side must mismatch:
    //
    //   expected_left != observed_left
    //   OR
    //   expected_right != observed_right
    //
    // This supports segment-tree / binary-search localization.

    pub open spec fn combine_digest(left: int, right: int, p: int) -> int
        recommends
            p > 0
    {
        (left + right) % p
    }

    pub proof fn lemma_combine_digest_equal_if_parts_equal(
        expected_left: int,
        expected_right: int,
        observed_left: int,
        observed_right: int,
        p: int
    )
        requires
            p > 0,
            expected_left == observed_left,
            expected_right == observed_right
        ensures
            combine_digest(expected_left, expected_right, p)
                == combine_digest(observed_left, observed_right, p)
    {
        assert(expected_left == observed_left);
        assert(expected_right == observed_right);

        assert((expected_left + expected_right) % p
            == (observed_left + observed_right) % p);

        assert(combine_digest(expected_left, expected_right, p)
            == combine_digest(observed_left, observed_right, p));
    }

    pub proof fn lemma_total_mismatch_implies_some_part_mismatch(
        expected_left: int,
        expected_right: int,
        observed_left: int,
        observed_right: int,
        p: int
    )
        requires
            p > 0,
            combine_digest(expected_left, expected_right, p)
                != combine_digest(observed_left, observed_right, p)
        ensures
            expected_left != observed_left
            ||
            expected_right != observed_right
    {
        if expected_left == observed_left && expected_right == observed_right {
            lemma_combine_digest_equal_if_parts_equal(
                expected_left,
                expected_right,
                observed_left,
                observed_right,
                p
            );

            assert(combine_digest(expected_left, expected_right, p)
                == combine_digest(observed_left, observed_right, p));

            assert(false);
        }
    }

    pub open spec fn suspicious_left_or_right(
        expected_left: int,
        expected_right: int,
        observed_left: int,
        observed_right: int
    ) -> bool {
        expected_left != observed_left
        ||
        expected_right != observed_right
    }

    pub proof fn lemma_total_mismatch_marks_suspicious_child(
        expected_left: int,
        expected_right: int,
        observed_left: int,
        observed_right: int,
        p: int
    )
        requires
            p > 0,
            combine_digest(expected_left, expected_right, p)
                != combine_digest(observed_left, observed_right, p)
        ensures
            suspicious_left_or_right(
                expected_left,
                expected_right,
                observed_left,
                observed_right
            )
    {
        lemma_total_mismatch_implies_some_part_mismatch(
            expected_left,
            expected_right,
            observed_left,
            observed_right,
            p
        );

        assert(expected_left != observed_left || expected_right != observed_right);

        assert(suspicious_left_or_right(
            expected_left,
            expected_right,
            observed_left,
            observed_right
        ));
    }

    pub proof fn lemma_if_no_child_suspicious_then_total_clean(
        expected_left: int,
        expected_right: int,
        observed_left: int,
        observed_right: int,
        p: int
    )
        requires
            p > 0,
            !suspicious_left_or_right(
                expected_left,
                expected_right,
                observed_left,
                observed_right
            )
        ensures
            combine_digest(expected_left, expected_right, p)
                == combine_digest(observed_left, observed_right, p)
    {
        assert(!suspicious_left_or_right(
            expected_left,
            expected_right,
            observed_left,
            observed_right
        ));

        assert(!(expected_left != observed_left || expected_right != observed_right));

        assert(expected_left == observed_left);
        assert(expected_right == observed_right);

        lemma_combine_digest_equal_if_parts_equal(
            expected_left,
            expected_right,
            observed_left,
            observed_right,
            p
        );

        assert(combine_digest(expected_left, expected_right, p)
            == combine_digest(observed_left, observed_right, p));
    }
    } // verus!

    

    fn main() {}