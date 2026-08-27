use vstd::prelude::*;

verus! {

pub open spec fn spec_pow(base: int, exp: int) -> int 
    decreases exp
{
    if exp <= 0 { 1 } else { base * spec_pow(base, exp - 1) }
}

/// MICRO-LEMMA 1: Focuses ONLY on the distributive property of modulo.
/// This is the "Atomic" step that usually causes the 12-minute hang.
proof fn lemma_mul_mod_distributive(a: int, b: int, p: int)
    requires p > 0
    ensures (a % p * b) % p == (a * b) % p
{
    // By isolating this, we prevent Z3 from looking at 'spec_pow' or 'exp'
    assert((a % p * b) % p == (a * b) % p) by(nonlinear_arith) requires p > 0;
}

/// MICRO-LEMMA 2: Connects the power spec to the multiplication step.
proof fn lemma_pow_mod_step(base: int, exp: int, p: int)
    requires p > 1, exp >= 0, base >= 0
    ensures (spec_pow(base, exp) % p * base) % p == spec_pow(base, exp + 1) % p
{
    reveal(spec_pow);
    // Chain the logic: (pow % p * base) % p  == (pow * base) % p == pow_next % p
    lemma_mul_mod_distributive(spec_pow(base, exp), base, p);
}

pub open spec fn ramanujan_sum(logs: Seq<u64>, q: int, p: int) -> int 
    decreases logs.len()
{
    if logs.len() == 0 { 0 } 
    else {
        let i = (logs.len() - 1) as int;
        let weight = spec_pow(q, i * i) % p;
        (ramanujan_sum(logs.drop_last(), q, p) + (logs.last() as int * weight)) % p
    }
}

pub struct RamanujanManager {
    pub state: u64,
    pub q: u64,
    pub p: u64,
}

impl RamanujanManager {
    pub fn calculate_weight(&self, i: u64) -> (res: u64)
        requires self.p > 1, i <= 31
        ensures res as int == spec_pow(self.q as int, (i * i) as int) % (self.p as int)
    {
        // Prove i*i is safe for u64 using a bit-vector hint
        assert(i * i <= 1000) by(bit_vector);
        
        let target_exp: u64 = i * i; 
        let mut res: u64 = 1;
        let mut curr: u64 = 0;

        proof { reveal(spec_pow); }

        while curr < target_exp 
            invariant 
                curr <= target_exp,
                self.p > 1,
                res as int == spec_pow(self.q as int, curr as int) % (self.p as int)
            decreases target_exp - curr 
        {
            let ghost old_curr = curr;
            // Use our micro-lemma to justify the next step
            proof { lemma_pow_mod_step(self.q as int, old_curr as int, self.p as int); }

            res = ((res as u128 * self.q as u128) % self.p as u128) as u64;
            curr = curr + 1;
        }
        res
    }

    pub fn process_logs(&mut self, logs: Vec<u64>) 
        requires 
            old(self).p > 1,
            old(self).state as int == ramanujan_sum(Seq::empty(), old(self).q as int, old(self).p as int)
    {
        let mut i: usize = 0;
        let n = logs.len();
        let ghost logs_seq = logs.view();
        
        while i < n 
            invariant
                i <= n,
                self.p == old(self).p,
                self.q == old(self).q,
                self.p > 1,
                self.state as int == ramanujan_sum(logs_seq.take(i as int), self.q as int, self.p as int)
            decreases n - i
        {
            if i >= 31 { break; } 

            let weight = self.calculate_weight(i as u64);
            
            proof {
                let seq_prev = logs_seq.take(i as int);
                let seq_curr = logs_seq.take((i + 1) as int);
                
                // Manually trigger the axioms of Sequence Extensionality
                assert(seq_curr.len() == i + 1);
                assert(seq_curr.drop_last() =~= seq_prev);
                
                reveal(ramanujan_sum);
                assert(seq_curr.last() == logs_seq.index(i as int));
            }

            // Intermediate u128 cast prevents overflow before modulo
            let term = (logs[i] as u128 * weight as u128) % (self.p as u128);
            self.state = ((self.state as u128 + term as u128) % (self.p as u128)) as u64;

            i = i + 1;
        }
    }
}
}

fn main() { }