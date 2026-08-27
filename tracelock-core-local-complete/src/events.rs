// src/events.rs
//
// Event model + deterministic canonicalization.
// In the real TimeFence system, these will come from eBPF/Falco/Tetragon/OTel/K8s.
// For now, we create stable event records and map them to u128 values.

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum EventKind {
    Exec,
    OpenFile,
    ReadFile,
    Connect,
    WriteFile,
    Exit,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TelemetryEvent {
    pub kind: EventKind,
    pub process: String,
    pub target: String,
    pub timestamp_ns: u64,
}

impl TelemetryEvent {
    pub fn new(
        kind: EventKind,
        process: impl Into<String>,
        target: impl Into<String>,
        timestamp_ns: u64,
    ) -> Self {
        Self {
            kind,
            process: process.into(),
            target: target.into(),
            timestamp_ns,
        }
    }

    pub fn canonical_string(&self) -> String {
        format!(
            "kind={:?}|process={}|target={}|timestamp_ns={}",
            self.kind, self.process, self.target, self.timestamp_ns
        )
    }

    pub fn to_field_element(&self, p: u128) -> u128 {
        let canon = self.canonical_string();

        let mut hasher = DefaultHasher::new();
        canon.hash(&mut hasher);

        let h = hasher.finish() as u128;
        h % p
    }
    pub fn short_label(&self) -> String {
    format!("{:?}:{}:{}", self.kind, self.process, self.target)
}
}

pub fn incident_events() -> Vec<TelemetryEvent> {
    vec![
        TelemetryEvent::new(EventKind::Exec, "bash", "/bin/bash", 100),
        TelemetryEvent::new(EventKind::OpenFile, "bash", "/var/run/secrets/token", 200),
        TelemetryEvent::new(EventKind::ReadFile, "bash", "/var/run/secrets/token", 300),
        TelemetryEvent::new(EventKind::Connect, "bash", "198.51.100.10:443", 400),
    ]
}

pub fn events_to_field_stream(events: &[TelemetryEvent], p: u128) -> Vec<u128> {
    events.iter().map(|e| e.to_field_element(p)).collect()
}



#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_canonical_stable() {
        let e = TelemetryEvent::new(EventKind::Exec, "bash", "/bin/bash", 100);

        let a = e.canonical_string();
        let b = e.canonical_string();

        assert_eq!(a, b);
    }

    #[test]
    fn test_event_hash_stable() {
        let p = 1_000_000_007;
        let e = TelemetryEvent::new(EventKind::Exec, "bash", "/bin/bash", 100);

        let a = e.to_field_element(p);
        let b = e.to_field_element(p);

        assert_eq!(a, b);
    }

    #[test]
    fn test_incident_events_to_stream() {
        let p = 1_000_000_007;
        let events = incident_events();
        let stream = events_to_field_stream(&events, p);

        assert_eq!(events.len(), 4);
        assert_eq!(stream.len(), 4);
    }
}