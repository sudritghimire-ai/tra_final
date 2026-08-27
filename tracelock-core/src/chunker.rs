// src/chunker.rs
//
// Chunking and localization.
// Splits a stream into chunks, checkpoints each chunk,
// then finds the first suspicious chunk.

use crate::checkpoint::TimeFenceCheckpoint;
use crate::ksentry::ksentry_fast;
use crate::verifier::{verify_checkpoint, VerificationReport};

#[derive(Debug, Clone)]
pub struct ChunkedStream {
    pub checkpoints: Vec<TimeFenceCheckpoint>,
}

pub fn chunk_stream(
    stream_id: &str,
    epoch: u64,
    xs: &[u128],
    chunk_size: usize,
    q: u128,
    p: u128,
) -> ChunkedStream {
    assert!(chunk_size > 0, "chunk_size must be > 0");

    let mut checkpoints = Vec::new();

    for (chunk_idx, chunk) in xs.chunks(chunk_size).enumerate() {
        let start_seq = (chunk_idx * chunk_size) as u64;
        let len = chunk.len() as u64;
        let digest = ksentry_fast(chunk, q, p).digest();

        checkpoints.push(TimeFenceCheckpoint::new(
            stream_id,
            epoch,
            start_seq,
            len,
            digest,
            q,
            p,
        ));
    }

    ChunkedStream { checkpoints }
}

pub fn verify_chunked_streams(
    expected: &ChunkedStream,
    observed: &ChunkedStream,
) -> Vec<VerificationReport> {
    expected
        .checkpoints
        .iter()
        .zip(observed.checkpoints.iter())
        .map(|(e, o)| verify_checkpoint(e, o))
        .collect()
}

pub fn first_bad_chunk_index(reports: &[VerificationReport]) -> Option<usize> {
    reports.iter().position(|r| r.is_suspicious())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fault::{inject_fault, FaultKind};
    use crate::verifier::VerificationStatus;

    #[test]
    fn test_chunk_count() {
        let q = 7;
        let p = 1_000_000_007;
        let xs = vec![1, 2, 3, 4, 5];

        let chunked = chunk_stream("s", 0, &xs, 2, q, p);

        assert_eq!(chunked.checkpoints.len(), 3);
        assert_eq!(chunked.checkpoints[0].start_seq, 0);
        assert_eq!(chunked.checkpoints[0].len, 2);
        assert_eq!(chunked.checkpoints[1].start_seq, 2);
        assert_eq!(chunked.checkpoints[1].len, 2);
        assert_eq!(chunked.checkpoints[2].start_seq, 4);
        assert_eq!(chunked.checkpoints[2].len, 1);
    }

    #[test]
    fn test_first_bad_chunk_for_swap() {
        let q = 7;
        let p = 1_000_000_007;

        let original = vec![101, 202, 303, 404, 505, 606];
        let observed = inject_fault(&original, FaultKind::SwapAdjacent);

        let expected_chunks = chunk_stream("s", 0, &original, 2, q, p);
        let observed_chunks = chunk_stream("s", 0, &observed, 2, q, p);

        let reports = verify_chunked_streams(&expected_chunks, &observed_chunks);
        let idx = first_bad_chunk_index(&reports).unwrap();

        assert_eq!(idx, 0);
        assert_eq!(reports[idx].status, VerificationStatus::DigestMismatch);
    }
}