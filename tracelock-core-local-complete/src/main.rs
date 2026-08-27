mod ksentry;
mod rolling;
mod antirebase;
mod checkpoint;
mod fault;
mod verifier;
mod incident;
mod chunker;
mod events;
mod bench;
mod report;
mod csv;
use ksentry::{ksentry_fast, ksentry_spec};
use rolling::{rolling_hash, rolling_rebase_digest, rolling_shifted_spec};
use antirebase::demo_ksentry_not_one_scalar_rebase;
use checkpoint::{CheckpointMismatch, TimeFenceCheckpoint};
use fault::{inject_fault, FaultKind};
use verifier::{verify_checkpoint, VerificationStatus};
use incident::{run_incident_suite, summarize_events};
use chunker::{chunk_stream, first_bad_chunk_index, verify_chunked_streams};
use events::{events_to_field_stream, incident_events};
use bench::benchmark_ksentry;
use report::{print_reports_for_cases, write_reports_json};
use csv::write_benchmark_csv;
fn main() {
    let q = 7u128;
    let p = 1_000_000_007u128;

    let stream = vec![101u128, 202, 303, 404];

    let fast = ksentry_fast(&stream, q, p);
    let slow = ksentry_spec(&stream, q, p);

    println!("K-Sentry fast digest: {}", fast.digest());
    println!("K-Sentry spec digest: {}", slow);
    println!("Position: {}", fast.position());

    if fast.digest() == slow {
        println!("OK: O(1) K-Sentry updater matches mathematical spec");
    } else {
        println!("ERROR: K-Sentry mismatch");
    }

    let ckpt = fast.checkpoint("node-1:runtime", 0);
    println!("K-Sentry checkpoint: {:?}", ckpt);

    println!("\n--- Rolling hash baseline ---");

    let rolling = rolling_hash(&stream, q, p);
    let shift = 10u64;

    let rebased = rolling_rebase_digest(rolling.digest(), q, p, shift);
    let shifted_spec = rolling_shifted_spec(&stream, q, p, shift);

    println!("Rolling local digest: {}", rolling.digest());
    println!("Rolling rebased digest at shift {}: {}", shift, rebased);
    println!("Rolling shifted spec at shift {}: {}", shift, shifted_spec);

    if rebased == shifted_spec {
        println!("BASELINE RESULT: rolling hash is digest-only rebaseable");
    }

    println!("\n--- K-Sentry anti-rebase demo ---");

if demo_ksentry_not_one_scalar_rebase(q, p) {
    println!("K-Sentry result: one scalar cannot rebase all triangular chunks");
    println!("This is the TimeFence anti-rebase advantage over rolling hash");
} else {
    println!("Unexpected: anti-rebase demo failed");
}


    println!("\n--- TimeFence checkpoint metadata demo ---");

    let expected = TimeFenceCheckpoint::new(
        "node-1:runtime",
        0,
        0,
        stream.len() as u64,
        fast.digest(),
        q,
        p,
    );

    let observed_same = TimeFenceCheckpoint::new(
        "node-1:runtime",
        0,
        0,
        stream.len() as u64,
        fast.digest(),
        q,
        p,
    );

    let observed_bad_len = TimeFenceCheckpoint::new(
        "node-1:runtime",
        0,
        0,
        stream.len() as u64 - 1,
        fast.digest(),
        q,
        p,
    );

    let observed_bad_digest = TimeFenceCheckpoint::new(
        "node-1:runtime",
        0,
        0,
        stream.len() as u64,
        fast.digest() + 1,
        q,
        p,
    );

    println!("Expected checkpoint: {:?}", expected);
    println!("Observed same reason: {:?}", expected.reason_mismatch(&observed_same));
    println!("Observed bad length reason: {:?}", expected.reason_mismatch(&observed_bad_len));
    println!("Observed bad digest reason: {:?}", expected.reason_mismatch(&observed_bad_digest));

    assert_eq!(expected.reason_mismatch(&observed_same), CheckpointMismatch::None);
    assert_eq!(expected.reason_mismatch(&observed_bad_len), CheckpointMismatch::Length);
    assert_eq!(expected.reason_mismatch(&observed_bad_digest), CheckpointMismatch::Digest);

        println!("\n--- Fault injection demo ---");

    let original = vec![101u128, 202, 303, 404];

    for fault in [
        FaultKind::None,
        FaultKind::DropOne,
        FaultKind::SwapAdjacent,
        FaultKind::DuplicateOne,
        FaultKind::TruncateTail,
        FaultKind::SpliceOldPrefix,
    ] {
        let attacked = inject_fault(&original, fault);

        let original_digest = ksentry_fast(&original, q, p).digest();
        let attacked_digest = ksentry_fast(&attacked, q, p).digest();

        println!(
            "{:?}: original_len={}, attacked_len={}, digest_match={}",
            fault,
            original.len(),
            attacked.len(),
            original_digest == attacked_digest
        );
    }


        println!("\n--- TimeFence verifier demo ---");

    let source_stream = vec![101u128, 202, 303, 404];
    let observed_stream = inject_fault(&source_stream, FaultKind::SwapAdjacent);

    let expected_digest = ksentry_fast(&source_stream, q, p).digest();
    let observed_digest = ksentry_fast(&observed_stream, q, p).digest();

    let expected_ckpt = TimeFenceCheckpoint::new(
        "node-1:runtime",
        0,
        0,
        source_stream.len() as u64,
        expected_digest,
        q,
        p,
    );

    let observed_ckpt = TimeFenceCheckpoint::new(
        "node-1:runtime",
        0,
        0,
        observed_stream.len() as u64,
        observed_digest,
        q,
        p,
    );

    let report = verify_checkpoint(&expected_ckpt, &observed_ckpt);

    println!("Source stream:   {:?}", source_stream);
    println!("Observed stream: {:?}", observed_stream);
    println!("Verification report: {:?}", report);

    match report.status {
        VerificationStatus::Clean => {
            println!("VERIFIER: clean window");
        }
        VerificationStatus::MetadataMismatch(reason) => {
            println!("VERIFIER: metadata mismatch: {:?}", reason);
        }
        VerificationStatus::DigestMismatch => {
            println!("VERIFIER: digest mismatch: same length but content/order changed");
        }
    }


      println!("\n--- End-to-end incident suite ---");

let cases = run_incident_suite(q, p);

for case in cases {
    println!(
        "\n{} | original_len={} observed_len={} | status={:?}",
        case.name,
        case.original_events.len(),
        case.observed_events.len(),
        case.report.status
    );

    println!("  original: {}", summarize_events(&case.original_events));
    println!("  observed: {}", summarize_events(&case.observed_events));
}
        println!("\n--- Chunk localization demo ---");

    let original = vec![101u128, 202, 303, 404, 505, 606];
    let observed = inject_fault(&original, FaultKind::SwapAdjacent);

    let expected_chunks = chunk_stream("node-1:runtime", 0, &original, 2, q, p);
    let observed_chunks = chunk_stream("node-1:runtime", 0, &observed, 2, q, p);

    let reports = verify_chunked_streams(&expected_chunks, &observed_chunks);

    if let Some(idx) = first_bad_chunk_index(&reports) {
        println!("First suspicious chunk index: {}", idx);
        println!("Suspicious report: {:?}", reports[idx]);
    } else {
        println!("No suspicious chunk found");
    }


        println!("\n--- Canonical event stream demo ---");

    let events = incident_events();
    let field_stream = events_to_field_stream(&events, p);

    for (event, x) in events.iter().zip(field_stream.iter()) {
        println!("{:?} -> field element {}", event, x);
    }

    let event_digest = ksentry_fast(&field_stream, q, p).digest();

    println!("K-Sentry digest over canonical events: {}", event_digest);

        println!("\n--- Local K-Sentry throughput benchmark ---");

    let bench = benchmark_ksentry(1_000_000, q, p);

    println!("Events: {}", bench.events);
    println!("Elapsed: {:.4?}", bench.elapsed);
    println!("Throughput: {:.2} events/sec", bench.events_per_sec);
    println!("Digest: {}", bench.digest);


    println!("\n--- Full TimeFence evidence reports ---");
let cases = run_incident_suite(q, p);
print_reports_for_cases(&cases);

let json_path = "timefence_report.json";

match write_reports_json(json_path, &cases) {
    Ok(_) => println!("Wrote evidence report JSON to {}", json_path),
    Err(e) => println!("Failed to write evidence report JSON: {}", e),
}
println!("\n--- Writing benchmark CSV ---");

let csv_path = "artifacts/bench.csv";

match write_benchmark_csv(csv_path, q, p) {
    Ok(_) => println!("Wrote benchmark CSV to {}", csv_path),
    Err(e) => println!("Failed to write benchmark CSV: {}", e),
}
}