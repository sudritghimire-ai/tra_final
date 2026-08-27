// src/bench.rs
//
// Simple local benchmark for K-Sentry throughput.
// This is not the final paper benchmark, but it gives your first
// measurable systems number: events/sec.

use std::time::{Duration, Instant};

use crate::ksentry::ksentry_fast;

#[derive(Debug, Clone)]
pub struct BenchResult {
    pub events: usize,
    pub elapsed: Duration,
    pub events_per_sec: f64,
    pub digest: u128,
}

pub fn generate_stream(n: usize) -> Vec<u128> {
    let mut xs = Vec::with_capacity(n);

    for i in 0..n {
        // Simple deterministic synthetic telemetry values.
        let x = ((i as u128 + 1) * 1_315_423_911u128) ^ ((i as u128) << 7);
        xs.push(x);
    }

    xs
}

pub fn benchmark_ksentry(n: usize, q: u128, p: u128) -> BenchResult {
    let xs = generate_stream(n);

    let start = Instant::now();
    let st = ksentry_fast(&xs, q, p);
    let elapsed = start.elapsed();

    let secs = elapsed.as_secs_f64();
    let events_per_sec = if secs > 0.0 {
        n as f64 / secs
    } else {
        f64::INFINITY
    };

    BenchResult {
        events: n,
        elapsed,
        events_per_sec,
        digest: st.digest(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_generate_stream_len() {
        let xs = generate_stream(100);
        assert_eq!(xs.len(), 100);
    }

    #[test]
    fn test_benchmark_runs() {
        let q = 7;
        let p = 1_000_000_007;

        let result = benchmark_ksentry(1_000, q, p);

        assert_eq!(result.events, 1_000);
        assert!(result.events_per_sec > 0.0);
    }
}