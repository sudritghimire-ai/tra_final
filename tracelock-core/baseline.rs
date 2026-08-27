use std::collections::BTreeMap;
use std::fs;
use std::time::Instant;

use hmac::{Hmac, Mac};
use sha2::Sha256;

use crate::ksentry::KSentry;

type HmacSha256 = Hmac<Sha256>;

#[derive(Debug, Clone)]
pub struct BaselineBenchRow {
    pub method: String,
    pub run: usize,
    pub events: usize,
    pub duration_ms: f64,
    pub events_per_sec: f64,
    pub digest: String,
}

#[derive(Debug, Clone)]
pub struct BaselineSummaryRow {
    pub method: String,
    pub runs: usize,
    pub events: usize,
    pub mean_events_per_sec: f64,
    pub min_events_per_sec: f64,
    pub max_events_per_sec: f64,
    pub stddev_events_per_sec: f64,
    pub mean_duration_ms: f64,
}

fn synthetic_event(i: u64) -> u128 {
    let mut x = i as u128;
    x ^= 0x9e3779b97f4a7c15u128;
    x = x.wrapping_mul(0xbf58476d1ce4e5b9u128);
    x ^= x >> 31;
    x = x.wrapping_mul(0x94d049bb133111ebu128);
    x ^= x >> 27;
    x
}

fn u128_to_bytes(x: u128) -> [u8; 16] {
    x.to_le_bytes()
}

fn hash_to_short_hex(hash: blake3::Hash) -> String {
    let bytes = hash.as_bytes();
    bytes[..8]
        .iter()
        .map(|b| format!("{:02x}", b))
        .collect::<String>()
}

fn bytes_to_short_hex(bytes: &[u8]) -> String {
    bytes[..8.min(bytes.len())]
        .iter()
        .map(|b| format!("{:02x}", b))
        .collect::<String>()
}

fn bench_ksentry(events: &[u128], q: u128, p: u128, run: usize) -> BaselineBenchRow {
    let start = Instant::now();

    let mut ks = KSentry::new(q, p);

    for &x in events {
        ks.update(x);
    }

    let elapsed = start.elapsed();
    let duration_ms = elapsed.as_secs_f64() * 1000.0;
    let events_per_sec = events.len() as f64 / elapsed.as_secs_f64();

    BaselineBenchRow {
        method: "ksentry_triangular".to_string(),
        run,
        events: events.len(),
        duration_ms,
        events_per_sec,
        digest: ks.digest().to_string(),
    }
}

fn bench_rolling_hash(events: &[u128], q: u128, p: u128, run: usize) -> BaselineBenchRow {
    let start = Instant::now();

    let mut acc = 0u128;
    let mut weight = 1u128;

    for &x in events {
        acc = (acc + ((x % p) * weight) % p) % p;
        weight = (weight * q) % p;
    }

    let elapsed = start.elapsed();
    let duration_ms = elapsed.as_secs_f64() * 1000.0;
    let events_per_sec = events.len() as f64 / elapsed.as_secs_f64();

    BaselineBenchRow {
        method: "rolling_hash_affine".to_string(),
        run,
        events: events.len(),
        duration_ms,
        events_per_sec,
        digest: acc.to_string(),
    }
}

fn bench_blake3_batch(events: &[u128], run: usize) -> BaselineBenchRow {
    let start = Instant::now();

    let mut hasher = blake3::Hasher::new();

    for &x in events {
        hasher.update(&u128_to_bytes(x));
    }

    let hash = hasher.finalize();

    let elapsed = start.elapsed();
    let duration_ms = elapsed.as_secs_f64() * 1000.0;
    let events_per_sec = events.len() as f64 / elapsed.as_secs_f64();

    BaselineBenchRow {
        method: "blake3_batch".to_string(),
        run,
        events: events.len(),
        duration_ms,
        events_per_sec,
        digest: hash_to_short_hex(hash),
    }
}

fn bench_hmac_sha256_batch(events: &[u128], run: usize) -> BaselineBenchRow {
    let start = Instant::now();

    let key = b"timefence-demo-key";
    let mut mac =
        HmacSha256::new_from_slice(key).expect("HMAC can take key of any size");

    for &x in events {
        mac.update(&u128_to_bytes(x));
    }

    let result = mac.finalize();
    let bytes = result.into_bytes();

    let elapsed = start.elapsed();
    let duration_ms = elapsed.as_secs_f64() * 1000.0;
    let events_per_sec = events.len() as f64 / elapsed.as_secs_f64();

    BaselineBenchRow {
        method: "hmac_sha256_batch".to_string(),
        run,
        events: events.len(),
        duration_ms,
        events_per_sec,
        digest: bytes_to_short_hex(&bytes),
    }
}

fn merkle_parent(left: blake3::Hash, right: blake3::Hash) -> blake3::Hash {
    let mut hasher = blake3::Hasher::new();
    hasher.update(left.as_bytes());
    hasher.update(right.as_bytes());
    hasher.finalize()
}

fn bench_merkle_chunks(events: &[u128], chunk_size: usize, run: usize) -> BaselineBenchRow {
    let start = Instant::now();

    let mut leaves: Vec<blake3::Hash> = Vec::new();

    for chunk in events.chunks(chunk_size) {
        let mut hasher = blake3::Hasher::new();

        for &x in chunk {
            hasher.update(&u128_to_bytes(x));
        }

        leaves.push(hasher.finalize());
    }

    if leaves.is_empty() {
        leaves.push(blake3::hash(&[]));
    }

    while leaves.len() > 1 {
        let mut next = Vec::with_capacity((leaves.len() + 1) / 2);

        let mut i = 0usize;
        while i < leaves.len() {
            if i + 1 < leaves.len() {
                next.push(merkle_parent(leaves[i], leaves[i + 1]));
            } else {
                next.push(leaves[i]);
            }

            i += 2;
        }

        leaves = next;
    }

    let root = leaves[0];

    let elapsed = start.elapsed();
    let duration_ms = elapsed.as_secs_f64() * 1000.0;
    let events_per_sec = events.len() as f64 / elapsed.as_secs_f64();

    BaselineBenchRow {
        method: format!("merkle_chunks_{}", chunk_size),
        run,
        events: events.len(),
        duration_ms,
        events_per_sec,
        digest: hash_to_short_hex(root),
    }
}

fn make_events(event_count: usize) -> Vec<u128> {
    let p = 1_000_000_007u128;

    (0..event_count)
        .map(|i| synthetic_event(i as u64) % p)
        .collect()
}

pub fn run_baseline_bench(event_count: usize) -> Vec<BaselineBenchRow> {
    run_baseline_bench_once(event_count, 0)
}

pub fn run_baseline_bench_once(event_count: usize, run: usize) -> Vec<BaselineBenchRow> {
    let q = 7u128;
    let p = 1_000_000_007u128;
    let events = make_events(event_count);

    vec![
        bench_ksentry(&events, q, p, run),
        bench_rolling_hash(&events, q, p, run),
        bench_blake3_batch(&events, run),
        bench_hmac_sha256_batch(&events, run),
        bench_merkle_chunks(&events, 1024, run),
    ]
}

pub fn run_repeated_baseline_bench(event_count: usize, runs: usize) -> Vec<BaselineBenchRow> {
    let mut rows = Vec::new();

    for run in 1..=runs {
        rows.extend(run_baseline_bench_once(event_count, run));
    }

    rows
}

fn summarize_rows(rows: &[BaselineBenchRow]) -> Vec<BaselineSummaryRow> {
    let mut groups: BTreeMap<String, Vec<&BaselineBenchRow>> = BTreeMap::new();

    for row in rows {
        groups.entry(row.method.clone()).or_default().push(row);
    }

    let mut summaries = Vec::new();

    for (method, group) in groups {
        let runs = group.len();
        let events = group[0].events;

        let throughputs: Vec<f64> = group.iter().map(|r| r.events_per_sec).collect();
        let durations: Vec<f64> = group.iter().map(|r| r.duration_ms).collect();

        let mean_events_per_sec =
            throughputs.iter().sum::<f64>() / throughputs.len() as f64;
        let mean_duration_ms = durations.iter().sum::<f64>() / durations.len() as f64;

        let min_events_per_sec = throughputs
            .iter()
            .copied()
            .fold(f64::INFINITY, f64::min);

        let max_events_per_sec = throughputs
            .iter()
            .copied()
            .fold(f64::NEG_INFINITY, f64::max);

        let variance = throughputs
            .iter()
            .map(|x| {
                let d = x - mean_events_per_sec;
                d * d
            })
            .sum::<f64>()
            / throughputs.len() as f64;

        let stddev_events_per_sec = variance.sqrt();

        summaries.push(BaselineSummaryRow {
            method,
            runs,
            events,
            mean_events_per_sec,
            min_events_per_sec,
            max_events_per_sec,
            stddev_events_per_sec,
            mean_duration_ms,
        });
    }

    summaries
}

pub fn write_baseline_bench_csv(path: &str, event_count: usize) -> std::io::Result<()> {
    let rows = run_baseline_bench(event_count);

    let mut csv = String::new();
    csv.push_str("method,run,events,duration_ms,events_per_sec,digest\n");

    for row in rows {
        csv.push_str(&format!(
            "{},{},{},{:.4},{:.2},{}\n",
            row.method,
            row.run,
            row.events,
            row.duration_ms,
            row.events_per_sec,
            row.digest
        ));
    }

    fs::write(path, csv)
}

pub fn write_repeated_baseline_bench_csv(
    path: &str,
    event_count: usize,
    runs: usize,
) -> std::io::Result<()> {
    let rows = run_repeated_baseline_bench(event_count, runs);

    let mut csv = String::new();
    csv.push_str("method,run,events,duration_ms,events_per_sec,digest\n");

    for row in rows {
        csv.push_str(&format!(
            "{},{},{},{:.4},{:.2},{}\n",
            row.method,
            row.run,
            row.events,
            row.duration_ms,
            row.events_per_sec,
            row.digest
        ));
    }

    fs::write(path, csv)
}

pub fn write_baseline_summary_csv(
    path: &str,
    event_count: usize,
    runs: usize,
) -> std::io::Result<()> {
    let rows = run_repeated_baseline_bench(event_count, runs);
    let summaries = summarize_rows(&rows);

    let mut csv = String::new();
    csv.push_str(
        "method,runs,events,mean_duration_ms,mean_events_per_sec,min_events_per_sec,max_events_per_sec,stddev_events_per_sec\n",
    );

    for row in summaries {
        csv.push_str(&format!(
            "{},{},{},{:.4},{:.2},{:.2},{:.2},{:.2}\n",
            row.method,
            row.runs,
            row.events,
            row.mean_duration_ms,
            row.mean_events_per_sec,
            row.min_events_per_sec,
            row.max_events_per_sec,
            row.stddev_events_per_sec
        ));
    }

    fs::write(path, csv)
}

pub fn write_all_baseline_outputs(
    artifact_dir: &str,
    event_count: usize,
    runs: usize,
) -> std::io::Result<()> {
    fs::create_dir_all(artifact_dir)?;

    write_baseline_bench_csv(
        &format!("{}/baseline_bench.csv", artifact_dir),
        event_count,
    )?;

    write_repeated_baseline_bench_csv(
        &format!("{}/baseline_bench_repeated.csv", artifact_dir),
        event_count,
        runs,
    )?;

    write_baseline_summary_csv(
        &format!("{}/baseline_bench_summary.csv", artifact_dir),
        event_count,
        runs,
    )?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_baseline_bench_runs() {
        let rows = run_baseline_bench(10_000);
        assert_eq!(rows.len(), 5);

        for row in rows {
            assert_eq!(row.events, 10_000);
            assert!(row.duration_ms >= 0.0);
            assert!(row.events_per_sec > 0.0);
            assert!(!row.digest.is_empty());
        }
    }

    #[test]
    fn test_repeated_baseline_bench_runs() {
        let rows = run_repeated_baseline_bench(1_000, 3);
        assert_eq!(rows.len(), 15);
    }

    #[test]
    fn test_write_all_baseline_outputs() {
        let dir = "baseline_test_artifacts";
        write_all_baseline_outputs(dir, 1_000, 2).unwrap();

        let one = fs::read_to_string(format!("{}/baseline_bench.csv", dir)).unwrap();
        let repeated =
            fs::read_to_string(format!("{}/baseline_bench_repeated.csv", dir)).unwrap();
        let summary =
            fs::read_to_string(format!("{}/baseline_bench_summary.csv", dir)).unwrap();

        assert!(one.contains("ksentry_triangular"));
        assert!(one.contains("hmac_sha256_batch"));
        assert!(repeated.contains("run"));
        assert!(summary.contains("mean_events_per_sec"));

        let _ = fs::remove_dir_all(dir);
    }
}