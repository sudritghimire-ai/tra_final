use std::time::Instant;

fn main() {
    let sizes = [1_000, 10_000, 50_000];

    for &n in &sizes {
        let logs: Vec<u64> = (0..n as u64).collect();

        let mut ks = KSentry {
            state: 0,
            q: 7,
            p: 1_000_000_007,
        };

        let start = Instant::now();
        ks.ingest_telemetry(logs);
        let duration = start.elapsed();

        let secs = duration.as_secs_f64();
        let throughput = n as f64 / secs;

        println!(
            "n = {}, time = {:.6} sec, throughput = {:.2} logs/sec",
            n, secs, throughput
        );
    }
}