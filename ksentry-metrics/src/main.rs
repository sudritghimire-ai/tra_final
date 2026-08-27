    use std::fs::File;
    use std::io::Write;
    use std::thread;
    use std::time::{Duration, Instant};

    use sysinfo::{CpuRefreshKind, MemoryRefreshKind, RefreshKind, System};

    #[derive(Clone, Debug)]
    pub struct KSentry {
        pub state: u64,
        pub q: u64,
        pub p: u64,
    }

    #[derive(Clone, Debug)]
    pub struct MismatchInfo {
        pub mismatch_exists: bool,
        pub first_index: Option<usize>,
        pub last_index: Option<usize>,
        pub mismatch_count: usize,
        pub mismatch_indices: Vec<usize>,
    }

    #[derive(Clone, Debug)]
    pub struct WindowLocalization {
        pub mismatch_exists: bool,
        pub start: Option<usize>,
        pub end: Option<usize>,
        pub original_window_state: Option<u64>,
        pub changed_window_state: Option<u64>,
        pub shifted_original_window_state: Option<u64>,
        pub shifted_changed_window_state: Option<u64>,
    }

    #[derive(Clone, Debug)]
    pub struct PrefixDivergence {
        pub divergence_exists: bool,
        pub first_prefix_index: Option<usize>,
        pub original_prefix_state: Option<u64>,
        pub changed_prefix_state: Option<u64>,
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
            .checked_mul(ii)
            .expect("weight_for_index: exponent overflow");
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

            let idx = offset
                .checked_add(j)
                .expect("shifted_state_for_logs: index overflow");

            let w = self.weight_for_index(idx);
            let term = Self::mul_mod_u64(li, w, self.p);
            state = Self::add_mod_u64(state, term, self.p);
            state %= self.p;
        }

        state
    }

        pub fn first_mismatch(&self, logs1: &[u64], logs2: &[u64]) -> Option<(usize, u64, u64)> {
            assert_eq!(logs1.len(), logs2.len(), "length mismatch");
            for i in 0..logs1.len() {
                if logs1[i] != logs2[i] {
                    return Some((i, logs1[i], logs2[i]));
                }
            }
            None
        }

        pub fn all_mismatch_indices(&self, logs1: &[u64], logs2: &[u64]) -> Vec<usize> {
            assert_eq!(logs1.len(), logs2.len(), "length mismatch");
            let mut out = Vec::new();
            for i in 0..logs1.len() {
                if logs1[i] != logs2[i] {
                    out.push(i);
                }
            }
            out
        }

        pub fn mismatch_info(&self, logs1: &[u64], logs2: &[u64]) -> MismatchInfo {
            assert_eq!(logs1.len(), logs2.len(), "length mismatch");
            let mismatch_indices = self.all_mismatch_indices(logs1, logs2);
            let mismatch_exists = !mismatch_indices.is_empty();

            MismatchInfo {
                mismatch_exists,
                first_index: mismatch_indices.first().copied(),
                last_index: mismatch_indices.last().copied(),
                mismatch_count: mismatch_indices.len(),
                mismatch_indices,
            }
        }

        pub fn mismatch_window(&self, logs1: &[u64], logs2: &[u64]) -> Option<(usize, usize)> {
            assert_eq!(logs1.len(), logs2.len(), "length mismatch");
            let first = self.first_mismatch(logs1, logs2).map(|x| x.0)?;
            let mut last = first;
            for i in (first..logs1.len()).rev() {
                if logs1[i] != logs2[i] {
                    last = i;
                    break;
                }
            }
            Some((first, last))
        }

        pub fn prefix_divergence(&self, logs1: &[u64], logs2: &[u64]) -> PrefixDivergence {
            assert_eq!(logs1.len(), logs2.len(), "length mismatch");

            let p1 = self.prefix_states(logs1);
            let p2 = self.prefix_states(logs2);

            for i in 0..p1.len() {
                if p1[i] != p2[i] {
                    return PrefixDivergence {
                        divergence_exists: true,
                        first_prefix_index: Some(i),
                        original_prefix_state: Some(p1[i]),
                        changed_prefix_state: Some(p2[i]),
                    };
                }
            }

            PrefixDivergence {
                divergence_exists: false,
                first_prefix_index: None,
                original_prefix_state: None,
                changed_prefix_state: None,
            }
        }

        pub fn localize_window(&self, logs1: &[u64], logs2: &[u64]) -> WindowLocalization {
            assert_eq!(logs1.len(), logs2.len(), "length mismatch");

            let Some((start, end)) = self.mismatch_window(logs1, logs2) else {
                return WindowLocalization {
                    mismatch_exists: false,
                    start: None,
                    end: None,
                    original_window_state: None,
                    changed_window_state: None,
                    shifted_original_window_state: None,
                    shifted_changed_window_state: None,
                };
            };

            let original_window = &logs1[start..=end];
            let changed_window = &logs2[start..=end];

            WindowLocalization {
                mismatch_exists: true,
                start: Some(start),
                end: Some(end),
                original_window_state: Some(self.state_for_logs(original_window)),
                changed_window_state: Some(self.state_for_logs(changed_window)),
                shifted_original_window_state: Some(self.shifted_state_for_logs(original_window, start)),
                shifted_changed_window_state: Some(self.shifted_state_for_logs(changed_window, start)),
            }
        }
    }

    // theorem-style collision probability upper bound:
    // Pr[collision] <= (n - 1)^2 / p
    fn collision_probability_bound(n: usize, p: u64) -> f64 {
        if n == 0 || p == 0 {
            return 0.0;
        }
        let d = (n.saturating_sub(1)) as f64;
        (d * d) / (p as f64)
    }

    // top 16 bits: cpu permille
    // low 48 bits: low 48 bits of mem_used
    fn pack(cpu_percent: f64, mem_raw: u64) -> u64 {
        let cpu_permille = (cpu_percent * 10.0).round().clamp(0.0, 1000.0) as u64;
        (cpu_permille << 48) | (mem_raw & 0x0000_FFFF_FFFF_FFFF)
    }

    fn detect_change(original: u64, changed: u64) -> bool {
        original != changed
    }

    fn test_swap_detection(ks: &KSentry, logs: &[u64]) -> Option<(usize, usize, u64, u64, bool, Vec<u64>)> {
        if logs.len() < 2 {
            return None;
        }

        let before = ks.state_for_logs(logs);
        let mut swapped = logs.to_vec();
        let j = swapped.len() - 1;
        swapped.swap(0, j);
        let after = ks.state_for_logs(&swapped);

        Some((0, j, before, after, before != after, swapped))
    }

    fn test_insertion_detection(
        ks: &KSentry,
        logs: &[u64],
        value: u64,
        pos: usize,
    ) -> (u64, u64, bool, Vec<u64>) {
        let original = ks.state_for_logs(logs);

        let mut inserted = logs.to_vec();
        let idx = pos.min(inserted.len());
        inserted.insert(idx, value);

        let inserted_state = ks.state_for_logs(&inserted);
        (original, inserted_state, original != inserted_state, inserted)
    }

    fn test_deletion_detection(ks: &KSentry, logs: &[u64], pos: usize) -> Option<(u64, u64, bool, Vec<u64>)> {
        if logs.is_empty() {
            return None;
        }

        let original = ks.state_for_logs(logs);
        let mut deleted = logs.to_vec();
        let idx = pos.min(deleted.len() - 1);
        deleted.remove(idx);

        let deleted_state = ks.state_for_logs(&deleted);
        Some((original, deleted_state, original != deleted_state, deleted))
    }

    fn test_truncation_detection(ks: &KSentry, logs: &[u64], keep: usize) -> Option<(u64, u64, bool, Vec<u64>)> {
        if logs.is_empty() || keep >= logs.len() {
            return None;
        }

        let original = ks.state_for_logs(logs);
        let truncated = logs[..keep].to_vec();
        let trunc_state = ks.state_for_logs(&truncated);

        Some((original, trunc_state, original != trunc_state, truncated))
    }

    fn test_composition_theorem(ks: &KSentry, logs: &[u64]) -> Option<(u64, u64, u64, u64, bool)> {
        if logs.len() < 2 {
            return None;
        }

        let mid = logs.len() / 2;
        let a = &logs[..mid];
        let b = &logs[mid..];

        let state_a = ks.state_for_logs(a);
        let shifted_b = ks.shifted_state_for_logs(b, a.len());
    let composed = ((state_a as u128 + shifted_b as u128) % (ks.p as u128)) as u64;
        let direct = ks.state_for_logs(logs);

        Some((state_a, shifted_b, composed, direct, composed == direct))
    }

    fn exhaustive_len2_collision_search(q: u64, p: u64, bound: u64) -> Option<((u64, u64), (u64, u64), u64)> {
        let ks = KSentry::new(q, p);

        for a in 0..=bound {
            for b in 0..=bound {
                let s1 = ks.state_for_logs(&[a, b]);

                for c in 0..=bound {
                    for d in 0..=bound {
                        if a == c && b == d {
                            continue;
                        }
                        let s2 = ks.state_for_logs(&[c, d]);
                        if s1 == s2 {
                            return Some(((a, b), (c, d), s1));
                        }
                    }
                }
            }
        }

        None
    }

    fn exhaustive_len3_collision_search(q: u64, p: u64, bound: u64) -> Option<((u64, u64, u64), (u64, u64, u64), u64)> {
        let ks = KSentry::new(q, p);

        for a in 0..=bound {
            for b in 0..=bound {
                for c in 0..=bound {
                    let s1 = ks.state_for_logs(&[a, b, c]);

                    for x in 0..=bound {
                        for y in 0..=bound {
                            for z in 0..=bound {
                                if a == x && b == y && c == z {
                                    continue;
                                }
                                let s2 = ks.state_for_logs(&[x, y, z]);
                                if s1 == s2 {
                                    return Some(((a, b, c), (x, y, z), s1));
                                }
                            }
                        }
                    }
                }
            }
        }

        None
    }

    fn print_localization_report(label: &str, ks: &KSentry, original: &[u64], changed: &[u64]) {
        println!("\n--- localization report: {} ---", label);

        if original.len() != changed.len() {
            println!(
                "length mismatch: original_len={} changed_len={}",
                original.len(),
                changed.len()
            );
            return;
        }

        let mismatch = ks.mismatch_info(original, changed);
        let prefix_div = ks.prefix_divergence(original, changed);
        let window = ks.localize_window(original, changed);

        println!("mismatch_exists           = {}", mismatch.mismatch_exists);
        println!("mismatch_count            = {}", mismatch.mismatch_count);
        println!("first_mismatch_index      = {:?}", mismatch.first_index);
        println!("last_mismatch_index       = {:?}", mismatch.last_index);

        if mismatch.mismatch_count <= 20 {
            println!("mismatch_indices          = {:?}", mismatch.mismatch_indices);
        } else {
            println!(
                "mismatch_indices          = first 20 {:?} ... total={}",
                &mismatch.mismatch_indices[..20],
                mismatch.mismatch_count
            );
        }

        if let Some((idx, old_v, new_v)) = ks.first_mismatch(original, changed) {
            println!("first_mismatch_old_value  = {}", old_v);
            println!("first_mismatch_new_value  = {}", new_v);

            let weight = ks.weight_for_index(idx);
            let old_term = KSentry::mul_mod_u64(old_v % ks.p, weight, ks.p);
            let new_term = KSentry::mul_mod_u64(new_v % ks.p, weight, ks.p);
            println!("first_mismatch_weight     = {}", weight);
            println!("first_mismatch_old_term   = {}", old_term);
            println!("first_mismatch_new_term   = {}", new_term);
        }

        println!("prefix_divergence_exists  = {}", prefix_div.divergence_exists);
        println!("first_prefix_index        = {:?}", prefix_div.first_prefix_index);
        println!("original_prefix_state     = {:?}", prefix_div.original_prefix_state);
        println!("changed_prefix_state      = {:?}", prefix_div.changed_prefix_state);

        println!("window_exists             = {}", window.mismatch_exists);
        println!("window_start              = {:?}", window.start);
        println!("window_end                = {:?}", window.end);
        println!("window_state_original     = {:?}", window.original_window_state);
        println!("window_state_changed      = {:?}", window.changed_window_state);
        println!("shifted_window_original   = {:?}", window.shifted_original_window_state);
        println!("shifted_window_changed    = {:?}", window.shifted_changed_window_state);

        if let (Some(a), Some(b)) = (window.shifted_original_window_state, window.shifted_changed_window_state) {
            println!("shifted_window_differs    = {}", a != b);
        }
    }

    fn main() {
        let q: u64 = 7;
        let p: u64 = 18_446_744_073_709_551_557; // 2^64 - 59

        let samples: usize = 20;
        let interval_ms: u64 = 500;

        let refresh = RefreshKind::new()
            .with_cpu(CpuRefreshKind::new().with_cpu_usage())
            .with_memory(MemoryRefreshKind::new().with_ram());

        let mut sys = System::new_with_specifics(refresh);

        sys.refresh_cpu();
        thread::sleep(Duration::from_millis(500));
        sys.refresh_cpu();

        let mut logs: Vec<u64> = Vec::with_capacity(samples);

        let mut raw_file = File::create("telemetry_results.csv").unwrap();
        writeln!(raw_file, "sample,cpu_percent,mem_used,log_entry").unwrap();

        let start_collect = Instant::now();

        for i in 0..samples {
            sys.refresh_cpu();
            sys.refresh_memory();

            let cpus = sys.cpus();
            let cpu_avg: f64 = if cpus.is_empty() {
                0.0
            } else {
                cpus.iter().map(|c| c.cpu_usage() as f64).sum::<f64>() / (cpus.len() as f64)
            };

            let mem = sys.used_memory();
            let entry = pack(cpu_avg, mem);
            logs.push(entry);

            println!(
                "sample_count={} cpu={:.2}% mem_used={} log_entry={}",
                i, cpu_avg, mem, entry
            );
            writeln!(raw_file, "{},{:.2},{},{}", i, cpu_avg, mem, entry).unwrap();

            thread::sleep(Duration::from_millis(interval_ms));
        }

        let collect_s = start_collect.elapsed().as_secs_f64();

        if !logs.is_empty() {
            logs.remove(0);
        }

        if logs.is_empty() {
            println!("No usable logs after warm-up drop.");
            return;
        }

        let ks = KSentry::new(q, p);

        let prefix_states = ks.prefix_states(&logs);
        let mut trace_file = File::create("telemetry_trace.csv").unwrap();
        writeln!(trace_file, "index,log_entry,prefix_integrity_state").unwrap();
        for (i, (&log, &state)) in logs.iter().zip(prefix_states.iter()).enumerate() {
            writeln!(trace_file, "{},{},{}", i, log, state).unwrap();
        }

        let small_collision_prob_bound = collision_probability_bound(logs.len(), p);

        // SECTION 1: integrity tests
        let small_state = ks.state_for_logs(&logs);

        let mut tampered = logs.clone();
        let mid = tampered.len() / 2;
        tampered[mid] ^= 1;
        let tampered_state = ks.state_for_logs(&tampered);

        let mut reordered = logs.clone();
        if reordered.len() >= 2 {
            let last = reordered.len() - 1;
            reordered.swap(0, last);
        }
        let reordered_state = ks.state_for_logs(&reordered);

        let swap_result = test_swap_detection(&ks, &logs);

        let insertion_value = 123456789u64;
        let (base_insert, inserted_state, insertion_detected, inserted_logs) =
            test_insertion_detection(&ks, &logs, insertion_value, logs.len() / 2);

        let deletion_result = test_deletion_detection(&ks, &logs, logs.len() / 2);
        let truncation_result = test_truncation_detection(&ks, &logs, logs.len() / 2);
        let composition_result = test_composition_theorem(&ks, &logs);

        let len2_bound = 5u64;
        let len3_bound = 3u64;

        let start_len2 = Instant::now();
        let len2_collision = exhaustive_len2_collision_search(q, p, len2_bound);
        let len2_time = start_len2.elapsed().as_secs_f64();

        let start_len3 = Instant::now();
        let len3_collision = exhaustive_len3_collision_search(q, p, len3_bound);
        let len3_time = start_len3.elapsed().as_secs_f64();

        let t0 = Instant::now();
        let small_state_check = ks.state_for_logs(&logs);
        let ingest_s = t0.elapsed().as_secs_f64();
        let throughput = (logs.len() as f64) / ingest_s.max(1e-12);

        println!("\n================ SECTION 1: INTEGRITY TESTS ================");
        println!("collected {} usable samples in {:.2}s", logs.len(), collect_s);
        println!("ingest_time = {:.6}s", ingest_s);
        println!("throughput = {:.2} logs/sec", throughput);
        println!("KSentry state (original)  = {}", small_state);
        println!("KSentry state check       = {}", small_state_check);
        println!("KSentry state (tampered)  = {}", tampered_state);
        println!("tamper_detected           = {}", detect_change(small_state, tampered_state));
        println!("KSentry state (reordered) = {}", reordered_state);
        println!("order_tamper_detected     = {}", detect_change(small_state, reordered_state));
        println!(
            "collision_prob_bound      <= {:.12e}  [=(n-1)^2 / p, n={}]",
            small_collision_prob_bound,
            logs.len()
        );

        if let Some((i, j, before, after, ok, swapped_logs)) = swap_result.clone() {
            println!("swap_test_indices         = ({}, {})", i, j);
            println!("swap_state_before         = {}", before);
            println!("swap_state_after          = {}", after);
            println!("swap_detected             = {}", ok);
            print_localization_report("swap", &ks, &logs, &swapped_logs);
        }

        println!("insertion_detected        = {}", insertion_detected);
        println!("insertion states          = {} -> {}", base_insert, inserted_state);
        println!(
            "insertion length change   = {} -> {}",
            logs.len(),
            inserted_logs.len()
        );

        print_localization_report("tampered-single-bit", &ks, &logs, &tampered);
        print_localization_report("reordered", &ks, &logs, &reordered);

        if let Some((orig, deleted, ok, deleted_logs)) = deletion_result.clone() {
            println!("deletion_detected         = {}", ok);
            println!("deletion states           = {} -> {}", orig, deleted);
            println!(
                "deletion length change    = {} -> {}",
                logs.len(),
                deleted_logs.len()
            );
        }

        if let Some((orig, trunc, ok, trunc_logs)) = truncation_result.clone() {
            println!("truncation_detected       = {}", ok);
            println!("truncation states         = {} -> {}", orig, trunc);
            println!(
                "truncation length change  = {} -> {}",
                logs.len(),
                trunc_logs.len()
            );
        }

        if let Some((state_a, shifted_b, composed, direct, ok)) = composition_result {
            println!("composition_state_a       = {}", state_a);
            println!("composition_shifted_b     = {}", shifted_b);
            println!("composition_composed      = {}", composed);
            println!("composition_direct        = {}", direct);
            println!("composition_holds         = {}", ok);
        }

        match len2_collision {
            None => {
                println!(
                    "len2 bounded collision search: NO collision found for bound={} (time {:.6}s)",
                    len2_bound, len2_time
                );
            }
            Some(((a, b), (c, d), s)) => {
                println!("len2 bounded collision search: COLLISION FOUND");
                println!("  ({},{}) and ({},{}) -> state {}", a, b, c, d, s);
                println!("  search time = {:.6}s", len2_time);
            }
        }

        match len3_collision {
            None => {
                println!(
                    "len3 bounded collision search: NO collision found for bound={} (time {:.6}s)",
                    len3_bound, len3_time
                );
            }
            Some(((a, b, c), (x, y, z), s)) => {
                println!("len3 bounded collision search: COLLISION FOUND");
                println!("  ({},{},{}) and ({},{},{}) -> state {}", a, b, c, x, y, z, s);
                println!("  search time = {:.6}s", len3_time);
            }
        }

        println!("\n--- example trace (first 5 logs) ---");
        for i in 0..logs.len().min(5) {
            println!(
                "i={} log_entry={} prefix_state={}",
                i, logs[i], prefix_states[i]
            );
        }

        // SECTION 2: performance tests
        println!("\n================ SECTION 2: PERFORMANCE TESTS ================");
        println!("---- 1,000,000 LOG EXPERIMENT ----");

        let big_n: usize = 1_000_000;
        let mut big_logs: Vec<u64> = Vec::with_capacity(big_n);
        for i in 0..big_n {
            big_logs.push(logs[i % logs.len()]);
        }

        let big_collision_prob_bound = collision_probability_bound(big_n, p);

        let t_big = Instant::now();
        let big_state = ks.state_for_logs(&big_logs);
        let ingest_big_s = t_big.elapsed().as_secs_f64();
        let throughput_big = (big_logs.len() as f64) / ingest_big_s.max(1e-12);

        let mut tampered_big = big_logs.clone();
        let mid_big = tampered_big.len() / 2;
        tampered_big[mid_big] ^= 1;
        let big_tampered_state = ks.state_for_logs(&tampered_big);

        let mut reordered_big = big_logs.clone();
        let last_big = reordered_big.len() - 1;
        reordered_big.swap(0, last_big);
        let big_reordered_state = ks.state_for_logs(&reordered_big);

        println!("ingest_time = {:.6}s", ingest_big_s);
        println!("throughput  = {:.2} logs/sec", throughput_big);
        println!("KSentry state (original)  = {}", big_state);
        println!("KSentry state (tampered)  = {}", big_tampered_state);
        println!("tamper_detected           = {}", detect_change(big_state, big_tampered_state));
        println!("KSentry state (reordered) = {}", big_reordered_state);
        println!("order_tamper_detected     = {}", detect_change(big_state, big_reordered_state));
        println!(
            "collision_prob_bound      <= {:.12e}  [=(n-1)^2 / p, n={}]",
            big_collision_prob_bound,
            big_n
        );

        let mut summary_file = File::create("ksentry_summary.txt").unwrap();
        writeln!(summary_file, "K-Sentry experiment summary").unwrap();
        writeln!(summary_file, "q = {}", q).unwrap();
        writeln!(summary_file, "p = {}", p).unwrap();

        writeln!(summary_file, "\n[SECTION 1: integrity tests]").unwrap();
        writeln!(summary_file, "small_run_logs = {}", logs.len()).unwrap();
        writeln!(summary_file, "small_run_collection_sec = {:.6}", collect_s).unwrap();
        writeln!(summary_file, "small_run_ingest_sec = {:.6}", ingest_s).unwrap();
        writeln!(summary_file, "small_run_throughput = {:.2}", throughput).unwrap();
        writeln!(summary_file, "small_run_state_original = {}", small_state).unwrap();
        writeln!(summary_file, "small_run_state_check = {}", small_state_check).unwrap();
        writeln!(summary_file, "small_run_state_tampered = {}", tampered_state).unwrap();
        writeln!(summary_file, "small_run_state_reordered = {}", reordered_state).unwrap();
        writeln!(
            summary_file,
            "small_run_collision_prob_bound = {:.12e}",
            small_collision_prob_bound
        )
        .unwrap();

        let tampered_mismatch = ks.mismatch_info(&logs, &tampered);
        let tampered_prefix_div = ks.prefix_divergence(&logs, &tampered);
        let tampered_window = ks.localize_window(&logs, &tampered);

        writeln!(summary_file, "tampered_mismatch_exists = {}", tampered_mismatch.mismatch_exists).unwrap();
        writeln!(summary_file, "tampered_mismatch_count = {}", tampered_mismatch.mismatch_count).unwrap();
        writeln!(summary_file, "tampered_first_index = {:?}", tampered_mismatch.first_index).unwrap();
        writeln!(summary_file, "tampered_last_index = {:?}", tampered_mismatch.last_index).unwrap();
        writeln!(
            summary_file,
            "tampered_prefix_divergence_exists = {}",
            tampered_prefix_div.divergence_exists
        )
        .unwrap();
        writeln!(
            summary_file,
            "tampered_prefix_divergence_index = {:?}",
            tampered_prefix_div.first_prefix_index
        )
        .unwrap();
        writeln!(summary_file, "tampered_window_start = {:?}", tampered_window.start).unwrap();
        writeln!(summary_file, "tampered_window_end = {:?}", tampered_window.end).unwrap();
        writeln!(
            summary_file,
            "tampered_shifted_window_original = {:?}",
            tampered_window.shifted_original_window_state
        )
        .unwrap();
        writeln!(
            summary_file,
            "tampered_shifted_window_changed = {:?}",
            tampered_window.shifted_changed_window_state
        )
        .unwrap();

        let reordered_mismatch = ks.mismatch_info(&logs, &reordered);
        let reordered_prefix_div = ks.prefix_divergence(&logs, &reordered);
        let reordered_window = ks.localize_window(&logs, &reordered);

        writeln!(summary_file, "reordered_mismatch_exists = {}", reordered_mismatch.mismatch_exists).unwrap();
        writeln!(summary_file, "reordered_mismatch_count = {}", reordered_mismatch.mismatch_count).unwrap();
        writeln!(summary_file, "reordered_first_index = {:?}", reordered_mismatch.first_index).unwrap();
        writeln!(summary_file, "reordered_last_index = {:?}", reordered_mismatch.last_index).unwrap();
        writeln!(
            summary_file,
            "reordered_prefix_divergence_exists = {}",
            reordered_prefix_div.divergence_exists
        )
        .unwrap();
        writeln!(
            summary_file,
            "reordered_prefix_divergence_index = {:?}",
            reordered_prefix_div.first_prefix_index
        )
        .unwrap();
        writeln!(summary_file, "reordered_window_start = {:?}", reordered_window.start).unwrap();
        writeln!(summary_file, "reordered_window_end = {:?}", reordered_window.end).unwrap();
        writeln!(
            summary_file,
            "reordered_shifted_window_original = {:?}",
            reordered_window.shifted_original_window_state
        )
        .unwrap();
        writeln!(
            summary_file,
            "reordered_shifted_window_changed = {:?}",
            reordered_window.shifted_changed_window_state
        )
        .unwrap();

        if let Some((i, j, before, after, ok, _swapped_logs)) = swap_result {
            writeln!(summary_file, "swap_test_i = {}", i).unwrap();
            writeln!(summary_file, "swap_test_j = {}", j).unwrap();
            writeln!(summary_file, "swap_state_before = {}", before).unwrap();
            writeln!(summary_file, "swap_state_after = {}", after).unwrap();
            writeln!(summary_file, "swap_detected = {}", ok).unwrap();
        }

        writeln!(summary_file, "insertion_detected = {}", insertion_detected).unwrap();
        writeln!(summary_file, "insertion_original = {}", base_insert).unwrap();
        writeln!(summary_file, "insertion_changed = {}", inserted_state).unwrap();

        if let Some((orig, deleted, ok, _)) = deletion_result {
            writeln!(summary_file, "deletion_detected = {}", ok).unwrap();
            writeln!(summary_file, "deletion_original = {}", orig).unwrap();
            writeln!(summary_file, "deletion_changed = {}", deleted).unwrap();
        }

        if let Some((orig, trunc, ok, _)) = truncation_result {
            writeln!(summary_file, "truncation_detected = {}", ok).unwrap();
            writeln!(summary_file, "truncation_original = {}", orig).unwrap();
            writeln!(summary_file, "truncation_changed = {}", trunc).unwrap();
        }

        if let Some((state_a, shifted_b, composed, direct, ok)) = composition_result {
            writeln!(summary_file, "composition_state_a = {}", state_a).unwrap();
            writeln!(summary_file, "composition_shifted_b = {}", shifted_b).unwrap();
            writeln!(summary_file, "composition_composed = {}", composed).unwrap();
            writeln!(summary_file, "composition_direct = {}", direct).unwrap();
            writeln!(summary_file, "composition_holds = {}", ok).unwrap();
        }

        writeln!(summary_file, "len2_bound = {}", len2_bound).unwrap();
        writeln!(summary_file, "len2_search_time_sec = {:.6}", len2_time).unwrap();
        writeln!(summary_file, "len2_collision_found = {}", len2_collision.is_some()).unwrap();
        if let Some(((a, b), (c, d), s)) = len2_collision {
            writeln!(summary_file, "len2_collision_a = {}", a).unwrap();
            writeln!(summary_file, "len2_collision_b = {}", b).unwrap();
            writeln!(summary_file, "len2_collision_c = {}", c).unwrap();
            writeln!(summary_file, "len2_collision_d = {}", d).unwrap();
            writeln!(summary_file, "len2_collision_state = {}", s).unwrap();
        }

        writeln!(summary_file, "len3_bound = {}", len3_bound).unwrap();
        writeln!(summary_file, "len3_search_time_sec = {:.6}", len3_time).unwrap();
        writeln!(summary_file, "len3_collision_found = {}", len3_collision.is_some()).unwrap();
        if let Some(((a, b, c), (x, y, z), s)) = len3_collision {
            writeln!(summary_file, "len3_collision_a = {}", a).unwrap();
            writeln!(summary_file, "len3_collision_b = {}", b).unwrap();
            writeln!(summary_file, "len3_collision_c = {}", c).unwrap();
            writeln!(summary_file, "len3_collision_x = {}", x).unwrap();
            writeln!(summary_file, "len3_collision_y = {}", y).unwrap();
            writeln!(summary_file, "len3_collision_z = {}", z).unwrap();
            writeln!(summary_file, "len3_collision_state = {}", s).unwrap();
        }

        writeln!(summary_file, "\n[SECTION 2: performance tests]").unwrap();
        writeln!(summary_file, "large_run_logs = {}", big_n).unwrap();
        writeln!(summary_file, "large_run_time_sec = {:.6}", ingest_big_s).unwrap();
        writeln!(summary_file, "large_run_throughput = {:.2}", throughput_big).unwrap();
        writeln!(summary_file, "large_run_state_original = {}", big_state).unwrap();
        writeln!(summary_file, "large_run_state_tampered = {}", big_tampered_state).unwrap();
        writeln!(summary_file, "large_run_state_reordered = {}", big_reordered_state).unwrap();
        writeln!(
            summary_file,
            "large_run_collision_prob_bound = {:.12e}",
            big_collision_prob_bound
        )
        .unwrap();

        println!("\nWrote telemetry_results.csv, telemetry_trace.csv, and ksentry_summary.txt.");
    }