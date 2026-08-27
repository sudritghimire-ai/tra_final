// src/verifier.rs
//
// TimeFence verifier.
//
// It compares an expected source-side checkpoint against an observed
// downstream checkpoint and classifies the evidence window.

use crate::checkpoint::{CheckpointMismatch, TimeFenceCheckpoint};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VerificationStatus {
    Clean,
    MetadataMismatch(CheckpointMismatch),
    DigestMismatch,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerificationReport {
    pub status: VerificationStatus,
    pub stream_id: String,
    pub epoch: u64,
    pub start_seq: u64,
    pub end_seq: u64,
    pub expected_digest: u128,
    pub observed_digest: u128,
}

impl VerificationReport {
    pub fn is_clean(&self) -> bool {
        self.status == VerificationStatus::Clean
    }

    pub fn is_suspicious(&self) -> bool {
        !self.is_clean()
    }
}

pub fn verify_checkpoint(
    expected: &TimeFenceCheckpoint,
    observed: &TimeFenceCheckpoint,
) -> VerificationReport {
    let reason = expected.reason_mismatch(observed);

    let status = match reason {
        CheckpointMismatch::None => VerificationStatus::Clean,
        CheckpointMismatch::Digest => VerificationStatus::DigestMismatch,
        other => VerificationStatus::MetadataMismatch(other),
    };

    VerificationReport {
        status,
        stream_id: expected.stream_id.clone(),
        epoch: expected.epoch,
        start_seq: expected.start_seq,
        end_seq: expected.end_seq,
        expected_digest: expected.digest,
        observed_digest: observed.digest,
    }
}

pub fn verify_many(
    expected: &[TimeFenceCheckpoint],
    observed: &[TimeFenceCheckpoint],
) -> Vec<VerificationReport> {
    expected
        .iter()
        .zip(observed.iter())
        .map(|(e, o)| verify_checkpoint(e, o))
        .collect()
}

pub fn first_suspicious_report(reports: &[VerificationReport]) -> Option<&VerificationReport> {
    reports.iter().find(|r| r.is_suspicious())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ckpt(len: u64, digest: u128) -> TimeFenceCheckpoint {
        TimeFenceCheckpoint::new("s", 0, 0, len, digest, 7, 1_000_000_007)
    }

    #[test]
    fn test_clean_checkpoint() {
        let expected = ckpt(4, 111);
        let observed = ckpt(4, 111);

        let report = verify_checkpoint(&expected, &observed);

        assert!(report.is_clean());
        assert_eq!(report.status, VerificationStatus::Clean);
    }

    #[test]
    fn test_digest_mismatch() {
        let expected = ckpt(4, 111);
        let observed = ckpt(4, 222);

        let report = verify_checkpoint(&expected, &observed);

        assert!(report.is_suspicious());
        assert_eq!(report.status, VerificationStatus::DigestMismatch);
    }

    #[test]
    fn test_length_metadata_mismatch() {
        let expected = ckpt(4, 111);
        let observed = ckpt(3, 111);

        let report = verify_checkpoint(&expected, &observed);

        assert!(report.is_suspicious());
        assert_eq!(
            report.status,
            VerificationStatus::MetadataMismatch(CheckpointMismatch::Length)
        );
    }

    #[test]
    fn test_first_suspicious_report() {
        let clean = verify_checkpoint(&ckpt(4, 111), &ckpt(4, 111));
        let bad = verify_checkpoint(&ckpt(4, 111), &ckpt(4, 222));

        let reports = vec![clean, bad];

        let first = first_suspicious_report(&reports).unwrap();

        assert_eq!(first.status, VerificationStatus::DigestMismatch);
    }
}