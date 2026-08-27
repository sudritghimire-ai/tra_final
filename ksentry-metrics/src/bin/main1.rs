use std::fs::File;
use std::io::Write;
use std::time::{Duration, Instant};

use sysinfo::System;

#[derive(Clone, Debug)]
pub struct KSentry {
    pub state: u64,
    pub q: u64,
    pub p: u64,
}

impl KSentry {
    pub fn new(q: u64, p: u64) -> Self {
        assert!(p > 1, "p must be > 1");
        assert!(q >= 1, "q must be >= 1");
        Self { state: 0, q, p }
    }

    #[inline]
    fn add_mod_u64(a: u64, b: u64, p: u64) -> u64 {
        let t = p - b;
        if a >= t { a - t } else { a + b }
    }

    #[inline]
    fn mul_mod_u64(a: u64, b: u64, p: u64) -> u64 {
        ((a as u128 * b as u128) % (p as u128)) as u64
    }

    #[inline]
    fn pow_mod_u64(base: u64, exp: u64, p: u64) -> u64 {
        let mut result = 1 % p;
        let mut b = base % p;
        let mut e = exp;

        while e > 0 {
            if e & 1 == 1 {
                result = Self::mul_mod_u64(result, b, p);
            }
            b = Self::mul_mod_u64(b, b, p);
            e >>= 1;
        }

        result
    }

    #[inline]
    fn weight_for_index(&self, i: usize) -> u64 {
    let ii = i as u64;
    let exp = ii
        .checked_mul(ii + 1)
        .expect("triangular exponent overflow")
        / 2;
    Self::pow_mod_u64(self.q, exp, self.p)
}

    pub fn ingest_telemetry(&mut self, logs: &[u64]) {
        self.state = 0;
        for (i, &li_raw) in logs.iter().enumerate() {
            let li = li_raw % self.p;
            let w = self.weight_for_index(i);
            let term = Self::mul_mod_u64(li, w, self.p);
            self.state = Self::add_mod_u64(self.state, term, self.p);
            self.state %= self.p;
        }
    }

    pub fn state_for_logs(&self, logs: &[u64]) -> u64 {
        let mut tmp = self.clone();
        tmp.ingest_telemetry(logs);
        tmp.state
    }

    pub fn prefix_states(&self, logs: &[u64]) -> Vec<u64> {
        let mut states = Vec::with_capacity(logs.len());
        let mut state = 0u64;

        for (i, &li_raw) in logs.iter().enumerate() {
            let li = li_raw % self.p;
            let w = self.weight_for_index(i);
            let term = Self::mul_mod_u64(li, w, self.p);
            state = Self::add_mod_u64(state, term, self.p);
            state %= self.p;
            states.push(state);
        }

        states
    }

    pub fn shifted_state_for_logs(&self, logs: &[u64], offset: usize) -> u64 {
        let mut state = 0u64;

        for (j, &li_raw) in logs.iter().enumerate() {
            let li = li_raw % self.p;
            let idx = offset.checked_add(j).expect("shifted index overflow");
            let w = self.weight_for_index(idx);
            let term = Self::mul_mod_u64(li, w, self.p);
            state = Self::add_mod_u64(state, term, self.p);
            state %= self.p;
        }

        state
    }

    pub fn term_at(&self, value: u64, index: usize) -> u64 {
        let li = value % self.p;
        let w = self.weight_for_index(index);
        Self::mul_mod_u64(li, w, self.p)
    }

    pub fn weight_at(&self, index: usize) -> u64 {
        self.weight_for_index(index)
    }
}

#[derive(Clone, Debug)]
struct MismatchInfo {
    mismatch_exists: bool,
    first_index: Option<usize>,
    last_index: Option<usize>,
    mismatch_count: usize,
    mismatch_indices: Vec<usize>,
}

fn mismatch_info(logs1: &[u64], logs2: &[u64]) -> MismatchInfo {
    let n = logs1.len().min(logs2.len());
    let mut indices = Vec::new();

    for i in 0..n {
        if logs1[i] != logs2[i] {
            indices.push(i);
        }
    }

    MismatchInfo {
        mismatch_exists: !indices.is_empty() || logs1.len() != logs2.len(),
        first_index: indices.first().copied(),
        last_index: indices.last().copied(),
        mismatch_count: indices.len() + logs1.len().max(logs2.len()) - n,
        mismatch_indices: indices,
    }
}

fn first_prefix_divergence(prefix1: &[u64], prefix2: &[u64]) -> Option<usize> {
    let n = prefix1.len().min(prefix2.len());
    (0..n).find(|&i| prefix1[i] != prefix2[i])
}
fn collision_probability_bound(n: usize, p: u64) -> f64 {
    if n <= 1 || p == 0 {
        return 0.0;
    }
    let n = n as f64;
    (n * (n - 1.0) / 2.0) / (p as f64)
}

fn detect_change(original: u64, changed: u64) -> bool {
    original != changed
}

fn pack(cpu_percent: f32, mem_used_bytes: u64) -> u64 {
    let cpu_scaled = (cpu_percent.max(0.0) as f64 * 1_000_000.0).round() as u64;
    ((cpu_scaled & 0xFF_FFFF) << 40) | (mem_used_bytes & 0xFF_FFFF_FFFF)
}

fn collect_live_logs(sample_count: usize, sample_every: Duration) -> (Vec<u64>, Vec<(usize, f32, u64, u64)>, f64) {
    let mut sys = System::new_all();
    let mut out_logs = Vec::with_capacity(sample_count);
    let mut rows = Vec::with_capacity(sample_count);

    sys.refresh_cpu();
    sys.refresh_memory();

    let start = Instant::now();

    for i in 0..sample_count {
        std::thread::sleep(sample_every);
        sys.refresh_cpu();
        sys.refresh_memory();

        let cpu = sys.global_cpu_info().cpu_usage();
        let mem_used_bytes = sys.used_memory() * 1024;
        let log_entry = pack(cpu, mem_used_bytes);

        println!(
            "sample_count={} cpu={:.2}% mem_used={} log_entry={}",
            i, cpu, mem_used_bytes, log_entry
        );

        out_logs.push(log_entry);
        rows.push((i, cpu, mem_used_bytes, log_entry));
    }

    let elapsed = start.elapsed().as_secs_f64();
    (out_logs, rows, elapsed)
}

fn run_edit_attack(logs: &[u64], idx: usize) -> Vec<u64> {
    let mut out = logs.to_vec();
    if !out.is_empty() {
        let i = idx.min(out.len() - 1);
        out[i] ^= 1;
    }
    out
}

fn run_reorder_attack(logs: &[u64]) -> (Vec<u64>, (usize, usize)) {
    let mut out = logs.to_vec();
    if out.len() >= 2 {
        let j = out.len() - 1;
        out.swap(0, j);
        (out, (0, j))
    } else {
        (out, (0, 0))
    }
}

fn run_insertion_attack(logs: &[u64], value: u64, pos: usize) -> Vec<u64> {
    let mut out = logs.to_vec();
    let idx = pos.min(out.len());
    out.insert(idx, value);
    out
}

fn run_deletion_attack(logs: &[u64], pos: usize) -> Vec<u64> {
    let mut out = logs.to_vec();
    if !out.is_empty() {
        let idx = pos.min(out.len() - 1);
        out.remove(idx);
    }
    out
}

fn run_truncation_attack(logs: &[u64], keep: usize) -> Vec<u64> {
    if keep >= logs.len() {
        logs.to_vec()
    } else {
        logs[..keep].to_vec()
    }
}

fn bounded_collision_search_len2(ks: &KSentry, bound: u64) -> bool {
    for a in 0..=bound {
        for b in 0..=bound {
            for c in 0..=bound {
                for d in 0..=bound {
                    if a == c && b == d {
                        continue;
                    }
                    let s1 = ks.state_for_logs(&[a, b]);
                    let s2 = ks.state_for_logs(&[c, d]);
                    if s1 == s2 {
                        return true;
                    }
                }
            }
        }
    }
    false
}

fn bounded_collision_search_len3(ks: &KSentry, bound: u64) -> bool {
    for a in 0..=bound {
        for b in 0..=bound {
            for c in 0..=bound {
                for d in 0..=bound {
                    for e in 0..=bound {
                        for f in 0..=bound {
                            if a == d && b == e && c == f {
                                continue;
                            }
                            let s1 = ks.state_for_logs(&[a, b, c]);
                            let s2 = ks.state_for_logs(&[d, e, f]);
                            if s1 == s2 {
                                return true;
                            }
                        }
                    }
                }
            }
        }
    }
    false
}

fn write_trace_csv(path: &str, rows: &[(usize, f32, u64, u64)], prefix: &[u64]) {
    let mut f = File::create(path).expect("failed to create telemetry_trace.csv");
    writeln!(f, "sample_index,cpu_percent,mem_used_bytes,log_entry,prefix_state").unwrap();

    for ((idx, cpu, mem, log), prefix_state) in rows.iter().zip(prefix.iter()) {
        writeln!(f, "{},{:.2},{},{},{}", idx, cpu, mem, log, prefix_state).unwrap();
    }
}

fn write_results_csv(
    path: &str,
    original: u64,
    tampered: u64,
    reordered: u64,
    inserted: u64,
    deleted: u64,
    truncated: u64,
) {
    let mut f = File::create(path).expect("failed to create telemetry_results.csv");
    writeln!(f, "trace_type,state").unwrap();
    writeln!(f, "original,{}", original).unwrap();
    writeln!(f, "tampered,{}", tampered).unwrap();
    writeln!(f, "reordered,{}", reordered).unwrap();
    writeln!(f, "inserted,{}", inserted).unwrap();
    writeln!(f, "deleted,{}", deleted).unwrap();
    writeln!(f, "truncated,{}", truncated).unwrap();
}

fn rolling_hash(logs: &[u64], base: u64, p: u64) -> u64 {
    let mut h = 0u64;
    for &x in logs {
        h = ((h as u128 * base as u128 + x as u128) % p as u128) as u64;
    }
    h
}

fn main() {
    let q: u64 = 7;
    let p: u64 = 18_446_744_073_709_551_557; // 2^64 - 59
    let ks = KSentry::new(q, p);

    // =========================
    // SECTION 1: LIVE EXPERIMENT
    // =========================
    let requested_samples = 20usize;
    let sample_every = Duration::from_millis(500);

    let (raw_logs, sample_rows, collection_secs) = collect_live_logs(requested_samples, sample_every);

    // match the style you showed: use first 19 usable samples
    let usable_logs: Vec<u64> = raw_logs.into_iter().take(19).collect();
    let usable_rows: Vec<(usize, f32, u64, u64)> = sample_rows.into_iter().take(19).collect();

    let prefix_states = ks.prefix_states(&usable_logs);

    let ingest_start = Instant::now();
    let original_state = ks.state_for_logs(&usable_logs);
    let ingest_secs = ingest_start.elapsed().as_secs_f64();

    let check_state = ks.state_for_logs(&usable_logs);

    let tamper_index = if usable_logs.is_empty() { 0 } else { usable_logs.len() / 2 };
    let tampered_logs = run_edit_attack(&usable_logs, tamper_index);
    let tampered_state = ks.state_for_logs(&tampered_logs);

    let (reordered_logs, swap_indices) = run_reorder_attack(&usable_logs);
    let reordered_state = ks.state_for_logs(&reordered_logs);

    let inserted_logs = run_insertion_attack(&usable_logs, 123_456_789, usable_logs.len() / 2);
    let inserted_state = ks.state_for_logs(&inserted_logs);

    let deleted_logs = run_deletion_attack(&usable_logs, usable_logs.len() / 2);
    let deleted_state = ks.state_for_logs(&deleted_logs);

    let truncated_logs = run_truncation_attack(&usable_logs, usable_logs.len() / 2);
    let truncated_state = ks.state_for_logs(&truncated_logs);

    let collision_bound = collision_probability_bound(usable_logs.len(), p);
    let throughput = (usable_logs.len() as f64) / ingest_secs.max(1e-12);

    let swap_before = original_state;
    let swap_after = reordered_state;

    let tamper_mismatch = mismatch_info(&usable_logs, &tampered_logs);
    let reorder_mismatch = mismatch_info(&usable_logs, &reordered_logs);

    let original_prefix = ks.prefix_states(&usable_logs);
    let tampered_prefix = ks.prefix_states(&tampered_logs);
    let reordered_prefix = ks.prefix_states(&reordered_logs);

    let tamper_first_prefix = first_prefix_divergence(&original_prefix, &tampered_prefix);
    let reorder_first_prefix = first_prefix_divergence(&original_prefix, &reordered_prefix);

    println!();
    println!("================ SECTION 1: INTEGRITY TESTS ================");
    println!("collected {} usable samples in {:.2}s", usable_logs.len(), collection_secs);
    println!("ingest_time = {:.6}s", ingest_secs);
    println!("throughput = {:.2} logs/sec", throughput);
    println!("KSentry state (original)  = {}", original_state);
    println!("KSentry state check       = {}", check_state);
    println!("KSentry state (tampered)  = {}", tampered_state);
    println!("tamper_detected           = {}", detect_change(original_state, tampered_state));
    println!("KSentry state (reordered) = {}", reordered_state);
    println!("order_tamper_detected     = {}", detect_change(original_state, reordered_state));
    println!(
        "collision_prob_bound      <= {:.12e}  [=n(n-1)/(2p), n={}]",
        collision_bound,
        usable_logs.len()
    );
    println!("swap_test_indices         = ({}, {})", swap_indices.0, swap_indices.1);
    println!("swap_state_before         = {}", swap_before);
    println!("swap_state_after          = {}", swap_after);
    println!("swap_detected             = {}", detect_change(swap_before, swap_after));

    println!();
    println!("--- localization report: swap ---");
    println!("mismatch_exists           = {}", reorder_mismatch.mismatch_exists);
    println!("mismatch_count            = {}", reorder_mismatch.mismatch_count);
    println!("first_mismatch_index      = {:?}", reorder_mismatch.first_index);
    println!("last_mismatch_index       = {:?}", reorder_mismatch.last_index);
    println!("mismatch_indices          = {:?}", reorder_mismatch.mismatch_indices);

    if let Some(i) = reorder_mismatch.first_index {
        println!("first_mismatch_old_value  = {}", usable_logs[i]);
        println!("first_mismatch_new_value  = {}", reordered_logs[i]);
        println!("first_mismatch_weight     = {}", ks.weight_at(i));
        println!("first_mismatch_old_term   = {}", ks.term_at(usable_logs[i], i));
        println!("first_mismatch_new_term   = {}", ks.term_at(reordered_logs[i], i));
    } else {
        println!("first_mismatch_old_value  = N/A");
        println!("first_mismatch_new_value  = N/A");
        println!("first_mismatch_weight     = N/A");
        println!("first_mismatch_old_term   = N/A");
        println!("first_mismatch_new_term   = N/A");
    }

    println!("prefix_divergence_exists  = {}", reorder_first_prefix.is_some());
    println!("first_prefix_index        = {:?}", reorder_first_prefix);
    println!(
        "original_prefix_state     = {:?}",
        reorder_first_prefix.map(|i| original_prefix[i])
    );
    println!(
        "changed_prefix_state      = {:?}",
        reorder_first_prefix.map(|i| reordered_prefix[i])
    );
    println!("window_exists             = {}", reorder_mismatch.first_index.is_some());
    println!("window_start              = {:?}", reorder_mismatch.first_index);
    println!("window_end                = {:?}", reorder_mismatch.last_index);
    println!(
        "window_state_original     = {:?}",
        Some(original_state)
    );
    println!(
        "window_state_changed      = {:?}",
        Some(reordered_state)
    );
    println!(
        "shifted_window_original   = {:?}",
        Some(ks.shifted_state_for_logs(&usable_logs, 0))
    );
    println!(
        "shifted_window_changed    = {:?}",
        Some(ks.shifted_state_for_logs(&reordered_logs, 0))
    );
    println!(
        "shifted_window_differs    = {}",
        ks.shifted_state_for_logs(&usable_logs, 0) != ks.shifted_state_for_logs(&reordered_logs, 0)
    );
    println!("insertion_detected        = {}", detect_change(original_state, inserted_state));
    println!("insertion states          = {} -> {}", original_state, inserted_state);
    println!("insertion length change   = {} -> {}", usable_logs.len(), inserted_logs.len());

    println!();
    println!("--- localization report: tampered-single-bit ---");
    println!("mismatch_exists           = {}", tamper_mismatch.mismatch_exists);
    println!("mismatch_count            = {}", tamper_mismatch.mismatch_count);
    println!("first_mismatch_index      = {:?}", tamper_mismatch.first_index);
    println!("last_mismatch_index       = {:?}", tamper_mismatch.last_index);
    println!("mismatch_indices          = {:?}", tamper_mismatch.mismatch_indices);

    if let Some(i) = tamper_mismatch.first_index {
        println!("first_mismatch_old_value  = {}", usable_logs[i]);
        println!("first_mismatch_new_value  = {}", tampered_logs[i]);
        println!("first_mismatch_weight     = {}", ks.weight_at(i));
        println!("first_mismatch_old_term   = {}", ks.term_at(usable_logs[i], i));
        println!("first_mismatch_new_term   = {}", ks.term_at(tampered_logs[i], i));
    } else {
        println!("first_mismatch_old_value  = N/A");
        println!("first_mismatch_new_value  = N/A");
        println!("first_mismatch_weight     = N/A");
        println!("first_mismatch_old_term   = N/A");
        println!("first_mismatch_new_term   = N/A");
    }

    println!("prefix_divergence_exists  = {}", tamper_first_prefix.is_some());
    println!("first_prefix_index        = {:?}", tamper_first_prefix);
    println!(
        "original_prefix_state     = {:?}",
        tamper_first_prefix.map(|i| original_prefix[i])
    );
    println!(
        "changed_prefix_state      = {:?}",
        tamper_first_prefix.map(|i| tampered_prefix[i])
    );
    println!("window_exists             = {}", tamper_mismatch.first_index.is_some());
    println!("window_start              = {:?}", tamper_mismatch.first_index);
    println!("window_end                = {:?}", tamper_mismatch.last_index);

    if let Some(i) = tamper_mismatch.first_index {
        println!("window_state_original     = {:?}", Some(usable_logs[i]));
        println!("window_state_changed      = {:?}", Some(tampered_logs[i]));
        println!("shifted_window_original   = {:?}", Some(ks.term_at(usable_logs[i], i)));
        println!("shifted_window_changed    = {:?}", Some(ks.term_at(tampered_logs[i], i)));
        println!(
            "shifted_window_differs    = {}",
            ks.term_at(usable_logs[i], i) != ks.term_at(tampered_logs[i], i)
        );
    } else {
        println!("window_state_original     = None");
        println!("window_state_changed      = None");
        println!("shifted_window_original   = None");
        println!("shifted_window_changed    = None");
        println!("shifted_window_differs    = false");
    }

    println!();
    println!("--- localization report: reordered ---");
    println!("mismatch_exists           = {}", reorder_mismatch.mismatch_exists);
    println!("mismatch_count            = {}", reorder_mismatch.mismatch_count);
    println!("first_mismatch_index      = {:?}", reorder_mismatch.first_index);
    println!("last_mismatch_index       = {:?}", reorder_mismatch.last_index);
    println!("mismatch_indices          = {:?}", reorder_mismatch.mismatch_indices);

    if let Some(i) = reorder_mismatch.first_index {
        println!("first_mismatch_old_value  = {}", usable_logs[i]);
        println!("first_mismatch_new_value  = {}", reordered_logs[i]);
        println!("first_mismatch_weight     = {}", ks.weight_at(i));
        println!("first_mismatch_old_term   = {}", ks.term_at(usable_logs[i], i));
        println!("first_mismatch_new_term   = {}", ks.term_at(reordered_logs[i], i));
    } else {
        println!("first_mismatch_old_value  = N/A");
        println!("first_mismatch_new_value  = N/A");
        println!("first_mismatch_weight     = N/A");
        println!("first_mismatch_old_term   = N/A");
        println!("first_mismatch_new_term   = N/A");
    }

    println!("prefix_divergence_exists  = {}", reorder_first_prefix.is_some());
    println!("first_prefix_index        = {:?}", reorder_first_prefix);
    println!(
        "original_prefix_state     = {:?}",
        reorder_first_prefix.map(|i| original_prefix[i])
    );
    println!(
        "changed_prefix_state      = {:?}",
        reorder_first_prefix.map(|i| reordered_prefix[i])
    );
    println!("window_exists             = {}", reorder_mismatch.first_index.is_some());
    println!("window_start              = {:?}", reorder_mismatch.first_index);
    println!("window_end                = {:?}", reorder_mismatch.last_index);
    println!("window_state_original     = {:?}", Some(original_state));
    println!("window_state_changed      = {:?}", Some(reordered_state));
    println!(
        "shifted_window_original   = {:?}",
        Some(ks.shifted_state_for_logs(&usable_logs, 0))
    );
    println!(
        "shifted_window_changed    = {:?}",
        Some(ks.shifted_state_for_logs(&reordered_logs, 0))
    );
    println!(
        "shifted_window_differs    = {}",
        ks.shifted_state_for_logs(&usable_logs, 0) != ks.shifted_state_for_logs(&reordered_logs, 0)
    );

    println!("deletion_detected         = {}", detect_change(original_state, deleted_state));
    println!("deletion states           = {} -> {}", original_state, deleted_state);
    println!("deletion length change    = {} -> {}", usable_logs.len(), deleted_logs.len());

    println!("truncation_detected       = {}", detect_change(original_state, truncated_state));
    println!("truncation states         = {} -> {}", original_state, truncated_state);
    println!("truncation length change  = {} -> {}", usable_logs.len(), truncated_logs.len());

    let mid = usable_logs.len() / 2;
    let a = &usable_logs[..mid];
    let b = &usable_logs[mid..];
    let composition_state_a = ks.state_for_logs(a);
    let composition_shifted_b = ks.shifted_state_for_logs(b, a.len());
    let composition_composed =
        ((composition_state_a as u128 + composition_shifted_b as u128) % (p as u128)) as u64;
    let composition_direct = ks.state_for_logs(&usable_logs);
    let composition_holds = composition_composed == composition_direct;

    println!("composition_state_a       = {}", composition_state_a);
    println!("composition_shifted_b     = {}", composition_shifted_b);
    println!("composition_composed      = {}", composition_composed);
    println!("composition_direct        = {}", composition_direct);
    println!("composition_holds         = {}", composition_holds);

    let c2_start = Instant::now();
    let collision2 = bounded_collision_search_len2(&ks, 5);
    let c2_secs = c2_start.elapsed().as_secs_f64();
    println!(
        "len2 bounded collision search: {} for bound=5 (time {:.6}s)",
        if collision2 { "collision found" } else { "NO collision found" },
        c2_secs
    );

    let c3_start = Instant::now();
    let collision3 = bounded_collision_search_len3(&ks, 3);
    let c3_secs = c3_start.elapsed().as_secs_f64();
    println!(
        "len3 bounded collision search: {} for bound=3 (time {:.6}s)",
        if collision3 { "collision found" } else { "NO collision found" },
        c3_secs
    );

    println!();
    println!("--- example trace (first 5 logs) ---");
    for i in 0..usable_logs.len().min(5) {
        println!(
            "i={} log_entry={} prefix_state={}",
            i, usable_logs[i], prefix_states[i]
        );
    }

    // =========================
    // SECTION 2: PERFORMANCE
    // =========================
    println!();
    println!("================ SECTION 2: PERFORMANCE TESTS ================");
    println!("---- 1,000,000 LOG EXPERIMENT ----");

    
    



let perf_logs: Vec<u64> = (0..1_000_000u64)
    .map(|i| ((i.wrapping_mul(1_103_515_245) ^ 12_345) << 8) ^ (i.rotate_left(13)))
    .collect();

let perf_t0 = Instant::now();
let perf_original = ks.state_for_logs(&perf_logs);
let perf_ingest_secs = perf_t0.elapsed().as_secs_f64();
let perf_throughput = (perf_logs.len() as f64) / perf_ingest_secs.max(1e-12);

let perf_tampered_logs = run_edit_attack(&perf_logs, perf_logs.len() / 2);
let perf_tampered = ks.state_for_logs(&perf_tampered_logs);

let (perf_reordered_logs, _) = run_reorder_attack(&perf_logs);
let perf_reordered = ks.state_for_logs(&perf_reordered_logs);

// Rolling hash baseline
let rh_t0 = Instant::now();
let rh_state = rolling_hash(&perf_logs, q, p);
let rh_secs = rh_t0.elapsed().as_secs_f64();
let rh_throughput = (perf_logs.len() as f64) / rh_secs.max(1e-12);

let rh_tampered = rolling_hash(&perf_tampered_logs, q, p);
let rh_reordered = rolling_hash(&perf_reordered_logs, q, p);

let perf_collision_bound = collision_probability_bound(perf_logs.len(), p);

println!("ingest_time = {:.6}s", perf_ingest_secs);
println!("throughput  = {:.2} logs/sec", perf_throughput);
println!("KSentry state (original)  = {}", perf_original);
println!("KSentry state (tampered)  = {}", perf_tampered);
println!("tamper_detected           = {}", detect_change(perf_original, perf_tampered));
println!("KSentry state (reordered) = {}", perf_reordered);
println!("order_tamper_detected     = {}", detect_change(perf_original, perf_reordered));

println!();
println!("--- BASELINE COMPARISON ---");
println!("Rolling hash throughput   = {:.2} logs/sec", rh_throughput);
println!("Rolling hash state        = {}", rh_state);
println!("Rolling tamper detected   = {}", detect_change(rh_state, rh_tampered));
println!("Rolling reorder detected  = {}", detect_change(rh_state, rh_reordered));

println!(
    "collision_prob_bound      <= {:.12e}  [=n(n-1)/(2p), n={}]",
    perf_collision_bound,
    perf_logs.len()
);

write_trace_csv("telemetry_trace.csv", &usable_rows, &prefix_states);
write_results_csv(
    "telemetry_results.csv",
    original_state,
    tampered_state,
    reordered_state,
    inserted_state,
    deleted_state,
    truncated_state,
);

let mut summary = File::create("ksentry_summary.txt").expect("failed to create ksentry_summary.txt");
writeln!(summary, "K-Sentry summary").unwrap();
writeln!(summary, "q = {}", q).unwrap();
writeln!(summary, "p = {}", p).unwrap();
writeln!(summary, "usable_samples = {}", usable_logs.len()).unwrap();
writeln!(summary, "collection_time_sec = {:.6}", collection_secs).unwrap();
writeln!(summary, "ingest_time_sec = {:.6}", ingest_secs).unwrap();
writeln!(summary, "throughput_logs_per_sec = {:.2}", throughput).unwrap();
writeln!(summary, "original_state = {}", original_state).unwrap();
writeln!(summary, "tampered_state = {}", tampered_state).unwrap();
writeln!(summary, "reordered_state = {}", reordered_state).unwrap();
writeln!(summary, "inserted_state = {}", inserted_state).unwrap();
writeln!(summary, "deleted_state = {}", deleted_state).unwrap();
writeln!(summary, "truncated_state = {}", truncated_state).unwrap();
writeln!(summary, "tamper_detected = {}", detect_change(original_state, tampered_state)).unwrap();
writeln!(summary, "order_tamper_detected = {}", detect_change(original_state, reordered_state)).unwrap();
writeln!(summary, "composition_holds = {}", composition_holds).unwrap();
writeln!(summary, "collision_prob_bound = {:.12e}", collision_bound).unwrap();

// optional: include baseline numbers in the summary file too
writeln!(summary, "rolling_hash_throughput_logs_per_sec = {:.2}", rh_throughput).unwrap();
writeln!(summary, "rolling_hash_tamper_detected = {}", detect_change(rh_state, rh_tampered)).unwrap();
writeln!(summary, "rolling_hash_reorder_detected = {}", detect_change(rh_state, rh_reordered)).unwrap();

println!();
println!("Wrote telemetry_results.csv, telemetry_trace.csv, and ksentry_summary.txt");
}
