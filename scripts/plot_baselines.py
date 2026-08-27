#!/usr/bin/env python3

import csv
from pathlib import Path

import matplotlib.pyplot as plt

ROOT = Path.home() / "k-sentry"
ARTIFACTS = ROOT / "artifacts"

INPUT = ARTIFACTS / "baseline_bench_summary.csv"
OUTPUT = ARTIFACTS / "baseline_throughput.png"

def short_name(method: str) -> str:
    names = {
        "rolling_hash_affine": "Rolling hash",
        "ksentry_triangular": "K-Sentry",
        "hmac_sha256_batch": "HMAC-SHA256",
        "blake3_batch": "BLAKE3",
        "merkle_chunks_1024": "Merkle chunks",
    }
    return names.get(method, method)

def main():
    if not INPUT.exists():
        raise SystemExit(f"Missing input file: {INPUT}")

    rows = []
    with INPUT.open(newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            rows.append({
                "method": row["method"],
                "label": short_name(row["method"]),
                "mean_eps": float(row["mean_events_per_sec"]),
                "stddev_eps": float(row["stddev_events_per_sec"]),
            })

    # Put fastest first
    rows.sort(key=lambda r: r["mean_eps"], reverse=True)

    labels = [r["label"] for r in rows]
    means_m = [r["mean_eps"] / 1_000_000 for r in rows]
    stddev_m = [r["stddev_eps"] / 1_000_000 for r in rows]

    plt.figure(figsize=(10, 6))
    bars = plt.bar(labels, means_m, yerr=stddev_m, capsize=5)

    plt.ylabel("Throughput (million events/sec)")
    plt.title("TraceLock Baseline Throughput Comparison")
    plt.xticks(rotation=20, ha="right")
    plt.tight_layout()

    for bar, value in zip(bars, means_m):
        height = bar.get_height()
        plt.text(
            bar.get_x() + bar.get_width() / 2,
            height,
            f"{value:.1f}M",
            ha="center",
            va="bottom",
            fontsize=9,
        )

    plt.savefig(OUTPUT, dpi=200)
    print(f"Wrote {OUTPUT}")

if __name__ == "__main__":
    main()
