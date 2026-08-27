#!/usr/bin/env bash
set -euo pipefail

ROOT="$HOME/k-sentry"
ARTIFACTS="$ROOT/artifacts"

echo "=== TraceLock eBPF Live Demo Runner ==="

mkdir -p "$ARTIFACTS"

cd "$ROOT/TraceLock-epbf"

echo
echo "[1/3] Building eBPF live collector..."
cargo build --release --package TraceLock-epbf

echo
echo "[2/3] Starting eBPF collector."
echo
echo "In another WSL terminal, run these commands:"
echo
echo "  echo secret-token >/tmp/TraceLock_live.txt"
echo "  cat /tmp/TraceLock_live.txt"
echo "  cat /etc/hostname"
echo "  curl -I http://example.com"
echo
echo "Collector will stop automatically after 30 kept events."
echo

sudo ./target/release/TraceLock-epbf

echo
echo "[3/3] Copying eBPF report..."

if [ -f "$ROOT/TraceLock-epbf/TraceLock_ebpf_filtered_report.txt" ]; then
    cp "$ROOT/TraceLock-epbf/TraceLock_ebpf_filtered_report.txt" "$ARTIFACTS/TraceLock_ebpf_exec_openat_connect_report.txt"
else
    echo "Warning: eBPF report not found."
fi

echo
echo "=== eBPF demo done ==="
echo "Artifacts:"
ls -lh "$ARTIFACTS"
