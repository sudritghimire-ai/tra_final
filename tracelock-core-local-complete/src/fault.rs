// src/fault.rs
//
// Fault injector for TimeFence experiments.
//
// These functions simulate what telemetry pipelines do under stress:
// drops, reorders, duplicates, truncation, and splice/replay.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FaultKind {
    None,
    DropOne,
    SwapAdjacent,
    DuplicateOne,
    TruncateTail,
    SpliceOldPrefix,
}

pub fn drop_one(xs: &[u128], index: usize) -> Vec<u128> {
    xs.iter()
        .enumerate()
        .filter_map(|(i, &x)| if i == index { None } else { Some(x) })
        .collect()
}

pub fn swap_adjacent(xs: &[u128], index: usize) -> Vec<u128> {
    let mut out = xs.to_vec();

    if index + 1 < out.len() {
        out.swap(index, index + 1);
    }

    out
}

pub fn duplicate_one(xs: &[u128], index: usize) -> Vec<u128> {
    let mut out = Vec::with_capacity(xs.len() + 1);

    for (i, &x) in xs.iter().enumerate() {
        out.push(x);

        if i == index {
            out.push(x);
        }
    }

    out
}

pub fn truncate_tail(xs: &[u128], new_len: usize) -> Vec<u128> {
    xs.iter().take(new_len).copied().collect()
}

pub fn splice_old_prefix(current: &[u128], old: &[u128], prefix_len: usize) -> Vec<u128> {
    let mut out = Vec::new();

    for &x in old.iter().take(prefix_len) {
        out.push(x);
    }

    for &x in current.iter().skip(prefix_len) {
        out.push(x);
    }

    out
}

pub fn inject_fault(xs: &[u128], kind: FaultKind) -> Vec<u128> {
    match kind {
        FaultKind::None => xs.to_vec(),
        FaultKind::DropOne => drop_one(xs, 1),
        FaultKind::SwapAdjacent => swap_adjacent(xs, 1),
        FaultKind::DuplicateOne => duplicate_one(xs, 1),
        FaultKind::TruncateTail => truncate_tail(xs, xs.len().saturating_sub(1)),
        FaultKind::SpliceOldPrefix => {
            let old = vec![999u128, 888, 777, 666];
            splice_old_prefix(xs, &old, 2)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_drop_one() {
        let xs = vec![10, 20, 30, 40];
        let out = drop_one(&xs, 1);

        assert_eq!(out, vec![10, 30, 40]);
    }

    #[test]
    fn test_swap_adjacent() {
        let xs = vec![10, 20, 30, 40];
        let out = swap_adjacent(&xs, 1);

        assert_eq!(out, vec![10, 30, 20, 40]);
    }

    #[test]
    fn test_duplicate_one() {
        let xs = vec![10, 20, 30, 40];
        let out = duplicate_one(&xs, 1);

        assert_eq!(out, vec![10, 20, 20, 30, 40]);
    }

    #[test]
    fn test_truncate_tail() {
        let xs = vec![10, 20, 30, 40];
        let out = truncate_tail(&xs, 2);

        assert_eq!(out, vec![10, 20]);
    }

    #[test]
    fn test_splice_old_prefix() {
        let current = vec![10, 20, 30, 40];
        let old = vec![99, 88, 77, 66];

        let out = splice_old_prefix(&current, &old, 2);

        assert_eq!(out, vec![99, 88, 30, 40]);
    }

    #[test]
    fn test_inject_faults() {
        let xs = vec![10, 20, 30, 40];

        assert_eq!(inject_fault(&xs, FaultKind::None), xs);
        assert_ne!(inject_fault(&xs, FaultKind::DropOne), xs);
        assert_ne!(inject_fault(&xs, FaultKind::SwapAdjacent), xs);
        assert_ne!(inject_fault(&xs, FaultKind::DuplicateOne), xs);
        assert_ne!(inject_fault(&xs, FaultKind::TruncateTail), xs);
        assert_ne!(inject_fault(&xs, FaultKind::SpliceOldPrefix), xs);
    }
}