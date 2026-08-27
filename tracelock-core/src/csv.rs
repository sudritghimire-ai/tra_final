// src/csv.rs
//
// CSV benchmark output for TimeFence local artifact.
// Writes benchmark rows to artifacts/bench.csv.

use std::fs;
use std::io;
use std::path::Path;

use crate::bench::benchmark_ksentry;

pub fn write_benchmark_csv(path: &str, q: u128, p: u128) -> io::Result<()> {
    let sizes = [1_000usize, 10_000usize, 100_000usize, 1_000_000usize];

    if let Some(parent) = Path::new(path).parent() {
        fs::create_dir_all(parent)?;
    }

    let mut csv = String::new();

    csv.push_str("events,elapsed_seconds,events_per_sec,digest\n");

    for n in sizes {
        let result = benchmark_ksentry(n, q, p);

        csv.push_str(&format!(
            "{},{:.9},{:.2},{}\n",
            result.events,
            result.elapsed.as_secs_f64(),
            result.events_per_sec,
            result.digest
        ));
    }

    fs::write(path, csv)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_write_benchmark_csv() {
        let q = 7;
        let p = 1_000_000_007;

        let path = "artifacts/test_bench.csv";

        write_benchmark_csv(path, q, p).expect("failed to write benchmark CSV");

        let contents = fs::read_to_string(path).expect("failed to read benchmark CSV");

        assert!(contents.contains("events,elapsed_seconds,events_per_sec,digest"));
        assert!(contents.contains("1000"));
    }
}