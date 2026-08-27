// src/report.rs
//
// Human-readable TimeFence evidence reports.
// Zero-dependency JSON export to avoid Windows Application Control
// blocking dependency build scripts.

use std::fs;
use std::io;

use crate::incident::{summarize_events, IncidentCase};
use crate::verifier::VerificationStatus;

#[derive(Debug, Clone)]
pub struct EvidenceReport {
    pub case_name: String,
    pub status: String,
    pub original_len: usize,
    pub observed_len: usize,
    pub expected_digest: u128,
    pub observed_digest: u128,
    pub original_timeline: String,
    pub observed_timeline: String,
    pub conclusion: String,
}

pub fn build_evidence_report(case: &IncidentCase) -> EvidenceReport {
    let status = format!("{:?}", case.report.status);

    let conclusion = match &case.report.status {
        VerificationStatus::Clean => {
            "clean: timeline evidence matches source checkpoint".to_string()
        }
        VerificationStatus::MetadataMismatch(reason) => {
            format!(
                "metadata mismatch: likely length/range/epoch/parameter problem: {:?}",
                reason
            )
        }
        VerificationStatus::DigestMismatch => {
            "digest mismatch: same range length, but content/order/splice changed".to_string()
        }
    };

    EvidenceReport {
        case_name: case.name.clone(),
        status,
        original_len: case.original_events.len(),
        observed_len: case.observed_events.len(),
        expected_digest: case.expected.digest,
        observed_digest: case.observed_ckpt.digest,
        original_timeline: summarize_events(&case.original_events),
        observed_timeline: summarize_events(&case.observed_events),
        conclusion,
    }
}

pub fn print_evidence_report(report: &EvidenceReport) {
    println!("\n================ TimeFence Evidence Report ================");
    println!("Case: {}", report.case_name);
    println!("Status: {}", report.status);
    println!(
        "Lengths: original={} observed={}",
        report.original_len, report.observed_len
    );
    println!("Expected digest: {}", report.expected_digest);
    println!("Observed digest: {}", report.observed_digest);
    println!("Original timeline:");
    println!("  {}", report.original_timeline);
    println!("Observed timeline:");
    println!("  {}", report.observed_timeline);
    println!("Conclusion:");
    println!("  {}", report.conclusion);
    println!("===========================================================\n");
}

pub fn print_reports_for_cases(cases: &[IncidentCase]) {
    for case in cases {
        let report = build_evidence_report(case);
        print_evidence_report(&report);
    }
}

fn json_escape(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
        .replace('\t', "\\t")
}

pub fn build_reports_for_cases(cases: &[IncidentCase]) -> Vec<EvidenceReport> {
    cases.iter().map(build_evidence_report).collect()
}

pub fn reports_to_json(reports: &[EvidenceReport]) -> String {
    let mut out = String::new();
    out.push_str("[\n");

    for (i, r) in reports.iter().enumerate() {
        out.push_str("  {\n");
        out.push_str(&format!(
            "    \"case_name\": \"{}\",\n",
            json_escape(&r.case_name)
        ));
        out.push_str(&format!(
            "    \"status\": \"{}\",\n",
            json_escape(&r.status)
        ));
        out.push_str(&format!("    \"original_len\": {},\n", r.original_len));
        out.push_str(&format!("    \"observed_len\": {},\n", r.observed_len));
        out.push_str(&format!(
            "    \"expected_digest\": {},\n",
            r.expected_digest
        ));
        out.push_str(&format!(
            "    \"observed_digest\": {},\n",
            r.observed_digest
        ));
        out.push_str(&format!(
            "    \"original_timeline\": \"{}\",\n",
            json_escape(&r.original_timeline)
        ));
        out.push_str(&format!(
            "    \"observed_timeline\": \"{}\",\n",
            json_escape(&r.observed_timeline)
        ));
        out.push_str(&format!(
            "    \"conclusion\": \"{}\"\n",
            json_escape(&r.conclusion)
        ));
        out.push_str("  }");

        if i + 1 != reports.len() {
            out.push(',');
        }

        out.push('\n');
    }

    out.push_str("]\n");
    out
}

pub fn write_reports_json(path: &str, cases: &[IncidentCase]) -> io::Result<()> {
    let reports = build_reports_for_cases(cases);
    let json = reports_to_json(&reports);
    fs::write(path, json)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::incident::run_incident_suite;

    #[test]
    fn test_build_evidence_report() {
        let q = 7;
        let p = 1_000_000_007;

        let cases = run_incident_suite(q, p);
        let report = build_evidence_report(&cases[0]);

        assert_eq!(report.case_name, "clean");
        assert!(report.conclusion.contains("clean"));
    }

    #[test]
    fn test_digest_mismatch_report() {
        let q = 7;
        let p = 1_000_000_007;

        let cases = run_incident_suite(q, p);
        let case = cases.iter().find(|c| c.name == "swap_adjacent").unwrap();

        let report = build_evidence_report(case);

        assert!(report.conclusion.contains("digest mismatch"));
    }

    #[test]
    fn test_reports_to_json() {
        let q = 7;
        let p = 1_000_000_007;

        let cases = run_incident_suite(q, p);
        let reports = build_reports_for_cases(&cases);
        let json = reports_to_json(&reports);

        assert!(json.contains("\"case_name\""));
        assert!(json.contains("\"conclusion\""));
        assert!(json.starts_with("["));
        assert!(json.ends_with("]\n"));
    }
}