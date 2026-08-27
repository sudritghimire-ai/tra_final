#!/usr/bin/env bash
set -euo pipefail

ROOT="$HOME/k-sentry"
ARTIFACTS="$ROOT/artifacts"

echo "=== TraceLock Full Local Artifact Runner ==="

mkdir -p "$ARTIFACTS"

echo
echo "[1/4] Running Verus proof artifact..."
cd "$ROOT/verus-x86-win"

if [ -f "./verus.exe" ]; then
    ./verus.exe ../proofs/finaltest_TraceLock_core_verified.rs
else
    echo "Skipping Verus: verus.exe not found in $ROOT/verus-x86-win"
fi

echo
echo "[2/4] Running TraceLock-core tests..."
cd "$ROOT/TraceLock-core"
cargo test

echo
echo "[3/4] Running TraceLock-core release demo..."
cargo run --release

echo
echo "[4/4] Running strace real-ingestion 3-case demo..."
cd "$ROOT/TraceLock-trace"
cargo run --release

echo
echo "Copying reports to artifacts/..."

if [ -f "$ROOT/TraceLock-core/TraceLock_report.json" ]; then
    cp "$ROOT/TraceLock-core/TraceLock_report.json" "$ARTIFACTS/TraceLock_report.json"
fi

if [ -f "$ROOT/TraceLock-core/artifacts/bench.csv" ]; then
    cp "$ROOT/TraceLock-core/artifacts/bench.csv" "$ARTIFACTS/bench.csv"
fi

if [ -f "$ROOT/TraceLock-trace/TraceLock_trace_3case_report.txt" ]; then
    cp "$ROOT/TraceLock-trace/TraceLock_trace_3case_report.txt" "$ARTIFACTS/TraceLock_trace_3case_report.txt"
fi

if [ -f "$ROOT/TraceLock-epbf/TraceLock_ebpf_filtered_report.txt" ]; then
    cp "$ROOT/TraceLock-epbf/TraceLock_ebpf_filtered_report.txt" "$ARTIFACTS/TraceLock_ebpf_exec_openat_connect_report.txt"
fi

echo
echo "=== Done ==="
echo "Artifacts:"
ls -lh "$ARTIFACTS"

# Copy baseline benchmark CSV
if [ -f "$ROOT/TraceLock-core/artifacts/baseline_bench.csv" ]; then
    cp "$ROOT/TraceLock-core/artifacts/baseline_bench.csv" "$ARTIFACTS/baseline_bench.csv"
fi
if [ -f "$ROOT/TraceLock-core/artifacts/baseline_bench_repeated.csv" ]; then
    cp "$ROOT/TraceLock-core/artifacts/baseline_bench_repeated.csv" "$ARTIFACTS/baseline_bench_repeated.csv"
fi

if [ -f "$ROOT/TraceLock-core/artifacts/baseline_bench_summary.csv" ]; then
    cp "$ROOT/TraceLock-core/artifacts/baseline_bench_summary.csv" "$ARTIFACTS/baseline_bench_summary.csv"
fi
echo "=== Done ==="
echo
echo "Generating benchmark graph..."
if command -v python3 >/dev/null 2>&1; then
    python3 "$ROOT/scripts/plot_baselines.py" || echo "Warning: graph generation failed"
else
    echo "Warning: python3 not found; skipping graph generation"
fi
ls -lh "$ARTIFACTS"