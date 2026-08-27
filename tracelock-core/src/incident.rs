// src/incident.rs
//
// End-to-end TimeFence incident demo using canonical telemetry events.
//
// Goal:
// Show a runtime-security timeline, inject telemetry faults,
// convert events to field elements, then classify whether the evidence
// window is clean, metadata-broken, or digest-broken.

use crate::checkpoint::TimeFenceCheckpoint;
use crate::events::{events_to_field_stream, incident_events, TelemetryEvent};
use crate::fault::FaultKind;
use crate::ksentry::ksentry_fast;
use crate::verifier::{verify_checkpoint, VerificationReport};

#[derive(Debug, Clone)]
pub struct IncidentCase {
    pub name: String,
    pub original_events: Vec<TelemetryEvent>,
    pub observed_events: Vec<TelemetryEvent>,
    pub original_stream: Vec<u128>,
    pub observed_stream: Vec<u128>,
    pub expected: TimeFenceCheckpoint,
    pub observed_ckpt: TimeFenceCheckpoint,
    pub report: VerificationReport,
}

fn inject_event_fault(events: &[TelemetryEvent], kind: FaultKind) -> Vec<TelemetryEvent> {
    match kind {
        FaultKind::None => events.to_vec(),

        FaultKind::DropOne => events
            .iter()
            .enumerate()
            .filter_map(|(i, e)| if i == 1 { None } else { Some(e.clone()) })
            .collect(),

        FaultKind::SwapAdjacent => {
            let mut out = events.to_vec();
            if out.len() > 2 {
                out.swap(1, 2);
            }
            out
        }

        FaultKind::DuplicateOne => {
            let mut out = Vec::with_capacity(events.len() + 1);
            for (i, e) in events.iter().enumerate() {
                out.push(e.clone());
                if i == 1 {
                    out.push(e.clone());
                }
            }
            out
        }

        FaultKind::TruncateTail => events
            .iter()
            .take(events.len().saturating_sub(1))
            .cloned()
            .collect(),

        FaultKind::SpliceOldPrefix => {
            let mut old = incident_events();
            if let Some(e) = old.get_mut(0) {
                e.process = "old-bash".to_string();
                e.timestamp_ns = 1;
            }
            if let Some(e) = old.get_mut(1) {
                e.target = "/old/secret/token".to_string();
                e.timestamp_ns = 2;
            }

            let prefix_len = 2usize;
            let mut out = Vec::new();

            for e in old.iter().take(prefix_len) {
                out.push(e.clone());
            }

            for e in events.iter().skip(prefix_len) {
                out.push(e.clone());
            }

            out
        }
    }
}

pub fn build_case(
    name: impl Into<String>,
    original_events: &[TelemetryEvent],
    fault: FaultKind,
    q: u128,
    p: u128,
) -> IncidentCase {
    let name = name.into();

    let observed_events = inject_event_fault(original_events, fault);

    let original_stream = events_to_field_stream(original_events, p);
    let observed_stream = events_to_field_stream(&observed_events, p);

    let expected_digest = ksentry_fast(&original_stream, q, p).digest();
    let observed_digest = ksentry_fast(&observed_stream, q, p).digest();

    let expected = TimeFenceCheckpoint::new(
        "node-1:runtime",
        0,
        0,
        original_stream.len() as u64,
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

    let report = verify_checkpoint(&expected, &observed_ckpt);

    IncidentCase {
        name,
        original_events: original_events.to_vec(),
        observed_events,
        original_stream,
        observed_stream,
        expected,
        observed_ckpt,
        report,
    }
}

pub fn run_incident_suite(q: u128, p: u128) -> Vec<IncidentCase> {
    let original_events = incident_events();

    vec![
        build_case("clean", &original_events, FaultKind::None, q, p),
        build_case("drop_one", &original_events, FaultKind::DropOne, q, p),
        build_case(
            "swap_adjacent",
            &original_events,
            FaultKind::SwapAdjacent,
            q,
            p,
        ),
        build_case(
            "duplicate_one",
            &original_events,
            FaultKind::DuplicateOne,
            q,
            p,
        ),
        build_case(
            "truncate_tail",
            &original_events,
            FaultKind::TruncateTail,
            q,
            p,
        ),
        build_case(
            "splice_old_prefix",
            &original_events,
            FaultKind::SpliceOldPrefix,
            q,
            p,
        ),
    ]
}

pub fn summarize_events(events: &[TelemetryEvent]) -> String {
    events
        .iter()
        .map(|e| e.short_label())
        .collect::<Vec<_>>()
        .join(" -> ")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::verifier::VerificationStatus;

    #[test]
    fn test_incident_suite_has_cases() {
        let q = 7;
        let p = 1_000_000_007;

        let cases = run_incident_suite(q, p);

        assert_eq!(cases.len(), 6);
    }

    #[test]
    fn test_clean_case_is_clean() {
        let q = 7;
        let p = 1_000_000_007;

        let cases = run_incident_suite(q, p);
        let clean = &cases[0];

        assert_eq!(clean.name, "clean");
        assert_eq!(clean.report.status, VerificationStatus::Clean);
    }

    #[test]
    fn test_swap_is_digest_mismatch() {
        let q = 7;
        let p = 1_000_000_007;

        let cases = run_incident_suite(q, p);
        let swap = cases.iter().find(|c| c.name == "swap_adjacent").unwrap();

        assert_eq!(swap.report.status, VerificationStatus::DigestMismatch);
    }

    #[test]
    fn test_drop_is_metadata_mismatch() {
        let q = 7;
        let p = 1_000_000_007;

        let cases = run_incident_suite(q, p);
        let drop = cases.iter().find(|c| c.name == "drop_one").unwrap();

        assert!(matches!(
            drop.report.status,
            VerificationStatus::MetadataMismatch(_)
        ));
    }

    #[test]
    fn test_splice_is_digest_mismatch() {
        let q = 7;
        let p = 1_000_000_007;

        let cases = run_incident_suite(q, p);
        let splice = cases
            .iter()
            .find(|c| c.name == "splice_old_prefix")
            .unwrap();

        assert_eq!(splice.report.status, VerificationStatus::DigestMismatch);
    }
}