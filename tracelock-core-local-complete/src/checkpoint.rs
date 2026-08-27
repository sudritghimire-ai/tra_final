// src/checkpoint.rs
//
// TimeFence checkpoint metadata.
//
// This is the production layer around K-Sentry:
// length-changing edits are caught by metadata,
// same-length/order/content edits are checked by digest.

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TimeFenceCheckpoint {
    pub stream_id: String,
    pub epoch: u64,
    pub start_seq: u64,
    pub end_seq: u64,
    pub len: u64,
    pub digest: u128,
    pub q: u128,
    pub p: u128,
}

impl TimeFenceCheckpoint {
    pub fn new(
        stream_id: impl Into<String>,
        epoch: u64,
        start_seq: u64,
        len: u64,
        digest: u128,
        q: u128,
        p: u128,
    ) -> Self {
        let end_seq = start_seq + len;

        Self {
            stream_id: stream_id.into(),
            epoch,
            start_seq,
            end_seq,
            len,
            digest,
            q,
            p,
        }
    }

    pub fn is_valid_range(&self) -> bool {
        self.end_seq == self.start_seq + self.len
    }

    pub fn same_range_as(&self, other: &Self) -> bool {
        self.stream_id == other.stream_id
            && self.epoch == other.epoch
            && self.start_seq == other.start_seq
            && self.end_seq == other.end_seq
            && self.len == other.len
    }

    pub fn same_params_as(&self, other: &Self) -> bool {
        self.q == other.q && self.p == other.p
    }

    pub fn digest_matches(&self, other: &Self) -> bool {
        self.digest == other.digest
    }

    pub fn fully_matches(&self, other: &Self) -> bool {
        self.same_range_as(other)
            && self.same_params_as(other)
            && self.digest_matches(other)
    }

    pub fn adjacent_to(&self, next: &Self) -> bool {
        self.stream_id == next.stream_id
            && self.epoch == next.epoch
            && self.end_seq == next.start_seq
    }

    pub fn reason_mismatch(&self, other: &Self) -> CheckpointMismatch {
        if self.stream_id != other.stream_id {
            return CheckpointMismatch::StreamId;
        }

        if self.epoch != other.epoch {
            return CheckpointMismatch::Epoch;
        }

        if self.start_seq != other.start_seq {
            return CheckpointMismatch::StartSeq;
        }

        if self.len != other.len {
            return CheckpointMismatch::Length;
        }

        if self.end_seq != other.end_seq {
            return CheckpointMismatch::EndSeq;
        }

        if self.q != other.q || self.p != other.p {
            return CheckpointMismatch::Params;
        }

        if self.digest != other.digest {
            return CheckpointMismatch::Digest;
        }

        CheckpointMismatch::None
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CheckpointMismatch {
    None,
    StreamId,
    Epoch,
    StartSeq,
    Length,
    EndSeq,
    Params,
    Digest,
}

impl CheckpointMismatch {
    pub fn is_clean(self) -> bool {
        self == CheckpointMismatch::None
    }

    pub fn is_metadata_mismatch(self) -> bool {
        matches!(
            self,
            CheckpointMismatch::StreamId
                | CheckpointMismatch::Epoch
                | CheckpointMismatch::StartSeq
                | CheckpointMismatch::Length
                | CheckpointMismatch::EndSeq
                | CheckpointMismatch::Params
        )
    }

    pub fn is_digest_mismatch(self) -> bool {
        self == CheckpointMismatch::Digest
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_checkpoint_range_valid() {
        let c = TimeFenceCheckpoint::new("node-1:runtime", 0, 10, 5, 12345, 7, 1_000_000_007);

        assert_eq!(c.start_seq, 10);
        assert_eq!(c.len, 5);
        assert_eq!(c.end_seq, 15);
        assert!(c.is_valid_range());
    }

    #[test]
    fn test_same_range() {
        let a = TimeFenceCheckpoint::new("s", 0, 0, 4, 111, 7, 1_000_000_007);
        let b = TimeFenceCheckpoint::new("s", 0, 0, 4, 222, 7, 1_000_000_007);

        assert!(a.same_range_as(&b));
        assert!(!a.digest_matches(&b));
    }

    #[test]
    fn test_length_mismatch_detected() {
        let expected = TimeFenceCheckpoint::new("s", 0, 0, 4, 111, 7, 1_000_000_007);
        let observed = TimeFenceCheckpoint::new("s", 0, 0, 3, 111, 7, 1_000_000_007);

        let reason = expected.reason_mismatch(&observed);

        assert_eq!(reason, CheckpointMismatch::Length);
        assert!(reason.is_metadata_mismatch());
    }

    #[test]
    fn test_digest_mismatch_detected() {
        let expected = TimeFenceCheckpoint::new("s", 0, 0, 4, 111, 7, 1_000_000_007);
        let observed = TimeFenceCheckpoint::new("s", 0, 0, 4, 999, 7, 1_000_000_007);

        let reason = expected.reason_mismatch(&observed);

        assert_eq!(reason, CheckpointMismatch::Digest);
        assert!(reason.is_digest_mismatch());
    }

    #[test]
    fn test_adjacent_chunks() {
        let a = TimeFenceCheckpoint::new("s", 0, 0, 4, 111, 7, 1_000_000_007);
        let b = TimeFenceCheckpoint::new("s", 0, 4, 3, 222, 7, 1_000_000_007);

        assert!(a.adjacent_to(&b));
    }
}