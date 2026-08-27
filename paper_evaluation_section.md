# Evaluation

This section evaluates TraceLock along five questions:

1. How fast is the verified streaming accumulator compared with common baselines?
2. How much overhead does the eBPF ingestion path add?
3. Can TraceLock detect real trace changes?
4. How does the prototype behave under stress?
5. Can TraceLock capture a mixed real workload?

## Experimental setup

All experiments were run locally in WSL on the TraceLock prototype. The artifact includes a verified K-Sentry core, a Rust `TraceLock-core` implementation, strace-based real-ingestion demos, and an eBPF ring-buffer collector for `execve`, `openat`, and `connect` tracepoints.

The K-Sentry accumulator used in the benchmark is the triangular O(1) streaming variant. The eBPF collector converts kernel events into canonical `TelemetryEvent` records, maps each event to a field element, and updates the K-Sentry digest online.

The main artifact outputs are:

- `artifacts/baseline_bench_summary.csv`
- `artifacts/baseline_throughput.png`
- `artifacts/TraceLock_trace_3case_report.txt`
- `artifacts/TraceLock_ebpf_exec_openat_connect_report.txt`
- `artifacts/overhead_file_read_summary.csv`
- `artifacts/resource_overhead_summary.md`
- `artifacts/collector_resource_summary.md`
- `artifacts/overload_report.txt`
- `artifacts/real_workload_report.txt`
- `artifacts/detection_latency_summary.csv`

## 1. Accumulator throughput

We compare K-Sentry against four baselines:

- affine rolling hash
- HMAC-SHA256 batch
- BLAKE3 batch
- Merkle chunk hashing

The benchmark uses 10 repeated runs over 1,000,000 synthetic scalar telemetry events.

| Method | Mean throughput |
|---|---:|
| Rolling hash affine | ~237.6M events/sec |
| K-Sentry triangular | ~176.3M events/sec |
| HMAC-SHA256 batch | ~140.4M events/sec |
| Merkle chunks | ~65.5M events/sec |
| BLAKE3 batch | ~65.5M events/sec |

K-Sentry is slower than affine rolling hash, but this is expected: affine rolling hash is the simple baseline that TraceLock argues is algebraically rebaseable. K-Sentry remains substantially faster than HMAC-SHA256, BLAKE3 batch hashing, and Merkle chunk hashing in this scalar-event benchmark.

The key takeaway is that TraceLock’s verified order-sensitive digest is not prohibitively expensive: it retains high throughput while escaping the affine rebase weakness of the rolling hash baseline.

## 2. Workload runtime overhead

We measured a 10-run, 5000-iteration file-read workload with and without the eBPF collector running.

| Mode | Mean runtime |
|---|---:|
| No collector | 10915.50 ms |
| With eBPF collector | 11009.51 ms |

The measured runtime overhead was:

| Metric | Value |
|---|---:|
| Runtime overhead | 0.86% |

This result suggests that, for this file-read workload, the eBPF collector adds low runtime overhead.

## 3. CPU and memory overhead

We also measured workload process CPU and memory usage on a 5-run, 5000-iteration file-read workload.

| Mode | Mean elapsed sec | Mean CPU % | Mean max RSS KB |
|---|---:|---:|---:|
| No collector | 10.8000 | 52.60 | 3584 |
| With eBPF collector | 10.8820 | 52.60 | 3584 |

The workload-level measurement showed:

- runtime overhead: 0.7593%
- CPU percent delta: 0.0000
- max RSS delta: 0 KB

This measurement captures the workload process resource usage, not the collector process itself.

## 4. Collector process resource usage

We separately sampled the actual `TraceLock-epbf` userspace collector process for 20 seconds during a stress workload.

| Metric | Value |
|---|---:|
| Samples | 21 |
| Mean CPU | 0.4476% |
| Max CPU | 1.9000% |
| Mean RSS | 17,776 KB |
| Mean VSZ | 20,540 KB |

The collector used low CPU and modest memory during the stress run. This closes the main caveat from the workload-only overhead experiment: the collector itself was also measured directly.

## 5. Real strace ingestion

The strace real-ingestion demo evaluates three cases:

| Case | Result |
|---|---|
| clean_vs_clean | CLEAN |
| clean_vs_extra_overwrite | METADATA_MISMATCH_LENGTH |
| clean_vs_same_length_change | DIGEST_MISMATCH_SAME_LENGTH |

This shows that TraceLock detects both extra/missing events and same-length trace changes on real Linux syscall traces.

The same-length case is especially important because the number of relevant events remains unchanged. The mismatch is detected by the K-Sentry digest rather than only by metadata.

## 6. End-to-end real-trace detection latency

We measured 10 runs of the full strace 3-case real-ingestion verifier.

| Metric | Value |
|---|---:|
| Mean full 3-case runtime | 348.45 ms |
| Minimum runtime | 340.01 ms |
| Maximum runtime | 358.41 ms |
| Standard deviation | 6.51 ms |

This is an end-to-end real-trace verification measurement. It includes spawning traced commands, parsing strace output, converting syscall lines into telemetry events, computing K-Sentry digests, and verifying clean, length-mismatch, and same-length mismatch cases. It is not merely digest-comparison latency.

## 7. Live eBPF telemetry

The eBPF collector attaches to:

- `syscalls:sys_enter_execve`
- `syscalls:sys_enter_openat`
- `syscalls:sys_enter_connect`

The live path is:

execve/openat/connect tracepoints
-> eBPF ring buffer
-> Rust userspace
-> TelemetryEvent
-> field element
-> K-Sentry digest
-> evidence report

The artifact report demonstrates that live kernel telemetry can be folded into K-Sentry evidence online.

## 8. Connect IP:port decoding

The eBPF connect parser decodes IPv4 `sockaddr` destinations.

Example observed event:

- `Connect:curl:34.223.124.45:80`

IPv6 and non-IPv4 destinations are currently reported as:

- `socket_connect_non_ipv4`

This is a limitation of the current prototype, but IPv4 destination decoding is already working.

## 9. Overload/stress behavior

The overload experiment uses a stress workload that generates exec, open, and connect events.

| Metric | Value |
|---|---:|
| stress_iterations | 2000 |
| kept_events | 120 |
| skipped_events | 2293 |
| final_digest | 980930368 |

Under stress, TraceLock continues producing ordered K-Sentry evidence, but the current prototype skips many events. This motivates future work on kernel-side filtering, larger ring buffers, backpressure accounting, and event-rate sweeps.

## 10. Real workload experiment

The real workload experiment runs:

- a Python HTTP server
- local file reads
- localhost curl requests
- an external curl request

Observed result:

| Metric | Value |
|---|---:|
| kept_events | 24 |
| skipped_events | 648 |
| final_digest | 795125924 |

Example observed events include:

- `OpenFile:/tmp/TraceLock_real_workload/secret.txt`
- `OpenFile:/etc/passwd`
- `Connect:socket_connect_non_ipv4`
- `Exec:bash`

This demonstrates that TraceLock can capture a mixed workload involving process execution, file access, and network activity, then fold those events into a live K-Sentry digest.

## Summary

The evaluation supports the following claims:

1. K-Sentry achieves high scalar-event throughput while avoiding the affine rolling-hash rebase weakness.
2. The eBPF collector adds low measured overhead on the evaluated file-read workload.
3. The actual collector process uses low CPU and modest memory during stress.
4. TraceLock detects extra/missing events and same-length trace changes on real Linux syscall traces.
5. TraceLock can ingest live exec/open/connect telemetry through eBPF and produce K-Sentry evidence reports.
6. The prototype can decode IPv4 connect destinations and capture mixed real workloads.

## Limitations

The current prototype still has important limitations:

1. IPv6 connect destinations are not decoded.
2. Some filtering is done in userspace rather than inside eBPF.
3. The Linux ingestion and eBPF code are tested and demonstrated, but not formally verified.
4. Overload behavior needs deeper study with ring-buffer size sweeps and event-rate sweeps.
5. The real workload evaluation should be expanded to larger workloads, such as package installation, build workloads, and long-running services.
6. The current evaluation is local and should be repeated on a native Linux machine outside WSL for stronger systems-paper evidence.
