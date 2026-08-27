# tracelock / K-Sentry

tracelock is a local prototype for evidence-preserving telemetry.

At the core is **K-Sentry**, a verified order-sensitive streaming accumulator. It turns a telemetry stream into compact evidence that depends on both event content and event position.

The goal is to help incident responders answer:

> Did this telemetry timeline remain ordered, complete, and trustworthy?

## What this artifact contains

```text
k-sentry/
  verus-x86-win/
    verus.exe
    finaltest2.rs

  proofs/
    finaltest_tracelock_core_verified.rs

  tracelock-core/
    src/
      ksentry.rs
      rolling.rs
      antirebase.rs
      checkpoint.rs
      fault.rs
      verifier.rs
      incident.rs
      chunker.rs
      events.rs
      bench.rs
      report.rs
      csv.rs

  artifacts/
    tracelock_report.json
    bench.csv

  scripts/
    run_demo.ps1