use std::fs;
use std::process::Command;

use timefence_core::events::{EventKind, TelemetryEvent};
use timefence_core::ksentry::KSentry;

#[derive(Debug, Clone)]
struct TraceEvent {
    event: TelemetryEvent,
    raw: String,
}

impl TraceEvent {
    fn to_field_element(&self, p: u128) -> u128 {
        self.event.to_field_element(p)
    }

    fn short_label(&self) -> String {
        self.event.short_label()
    }
}

#[derive(Debug, Clone)]
struct TraceRun {
    name: String,
    raw_syscall_lines_seen: usize,
    events: Vec<TraceEvent>,
    digest: u128,
}

impl TraceRun {
    fn len(&self) -> usize {
        self.events.len()
    }

    fn timeline(&self) -> String {
        self.events
            .iter()
            .map(|e| e.short_label())
            .collect::<Vec<_>>()
            .join(" -> ")
    }
}

#[derive(Debug, Clone)]
struct CompareCase {
    name: String,
    expected: TraceRun,
    observed: TraceRun,
    status: String,
}

fn extract_quoted_arg(line: &str) -> Option<String> {
    let start = line.find('"')?;
    let rest = &line[start + 1..];
    let end = rest.find('"')?;
    Some(rest[..end].to_string())
}

fn is_noise_path(path: &str) -> bool {
    path.contains("libc.so")
        || path.contains("ld.so.cache")
        || path.contains("/usr/lib/locale")
        || path.contains("/usr/share/locale")
        || path.contains("/gconv/")
        || path.contains("/rustup/")
        || path.contains("/target/release/deps")
}

fn is_relevant_path(path: &str) -> bool {
    path.contains("/tmp/timefence_clean.txt")
        || path.contains("/tmp/timefence_observed.txt")
        || path.contains("/tmp/timefence_extra.txt")
        || path.contains("/tmp/timefence_demo.txt")
        || path.contains("secret")
        || path.contains("token")
        || path.contains("/etc/passwd")
        || path.contains("/bin/bash")
        || path.contains("/usr/bin/bash")
        || path.contains("/usr/bin/cat")
}

fn parse_strace_line(line: &str) -> Option<TraceEvent> {
    if line.contains("execve(") {
        let target = extract_quoted_arg(line).unwrap_or_else(|| "unknown_exec".to_string());

        if is_noise_path(&target) {
            return None;
        }

        return Some(TraceEvent {
            event: TelemetryEvent::new(
                EventKind::Exec,
                "strace-target",
                target,
                0,
            ),
            raw: line.to_string(),
        });
    }

    if line.contains("openat(") || line.contains("open(") {
        let target = extract_quoted_arg(line).unwrap_or_else(|| "unknown_file".to_string());

        if is_noise_path(&target) {
            return None;
        }

        if !is_relevant_path(&target) {
            return None;
        }

        return Some(TraceEvent {
            event: TelemetryEvent::new(
                EventKind::OpenFile,
                "strace-target",
                target,
                0,
            ),
            raw: line.to_string(),
        });
    }

    if line.contains("connect(") {
        return Some(TraceEvent {
            event: TelemetryEvent::new(
                EventKind::Connect,
                "strace-target",
                "socket_connect",
                0,
            ),
            raw: line.to_string(),
        });
    }

    None
}

fn run_strace_script(script: &str) -> Vec<String> {
    let output = Command::new("strace")
        .args([
            "-f",
            "-e",
            "trace=execve,open,openat,connect",
            "bash",
            "-c",
            script,
        ])
        .output()
        .expect("failed to run strace");

    let stderr = String::from_utf8_lossy(&output.stderr);
    stderr.lines().map(|s| s.to_string()).collect()
}

fn build_trace_run(name: &str, script: &str, q: u128, p: u128) -> TraceRun {
    let lines = run_strace_script(script);

    let mut raw_syscall_lines_seen = 0usize;
    let mut events = Vec::new();

    for line in lines {
        if line.contains("execve(")
            || line.contains("openat(")
            || line.contains("open(")
            || line.contains("connect(")
        {
            raw_syscall_lines_seen += 1;
        }

        if let Some(event) = parse_strace_line(&line) {
            events.push(event);
        }
    }

    let mut ks = KSentry::new(q, p);

    for event in &events {
        let x = event.to_field_element(p);
        ks.update(x);
    }

    TraceRun {
        name: name.to_string(),
        raw_syscall_lines_seen,
        events,
        digest: ks.digest(),
    }
}

fn compare_trace_runs(expected: &TraceRun, observed: &TraceRun) -> String {
    if expected.len() != observed.len() {
        "METADATA_MISMATCH_LENGTH".to_string()
    } else if expected.digest != observed.digest {
        "DIGEST_MISMATCH_SAME_LENGTH".to_string()
    } else {
        "CLEAN".to_string()
    }
}

fn print_trace_run(run: &TraceRun, p: u128) {
    println!("\n--- {} trace ---", run.name);
    println!("raw_syscall_lines_seen={}", run.raw_syscall_lines_seen);
    println!("relevant_events={}", run.len());
    println!("digest={}", run.digest);

    for event in &run.events {
        let x = event.to_field_element(p);
        println!("{:?} -> x={}", event.event, x);
        println!("  raw: {}", event.raw);
    }
}

fn build_case(
    case_name: &str,
    expected_script: &str,
    observed_script: &str,
    q: u128,
    p: u128,
) -> CompareCase {
    let expected = build_trace_run(&format!("{}-expected", case_name), expected_script, q, p);
    let observed = build_trace_run(&format!("{}-observed", case_name), observed_script, q, p);
    let status = compare_trace_runs(&expected, &observed);

    CompareCase {
        name: case_name.to_string(),
        expected,
        observed,
        status,
    }
}

fn print_case_summary(case: &CompareCase) {
    println!("\n====================================================");
    println!("Case: {}", case.name);
    println!("Status: {}", case.status);
    println!(
        "Expected events={}, digest={}",
        case.expected.len(),
        case.expected.digest
    );
    println!(
        "Observed events={}, digest={}",
        case.observed.len(),
        case.observed.digest
    );

    match case.status.as_str() {
        "CLEAN" => {
            println!("VERIFIER: clean real trace");
        }
        "METADATA_MISMATCH_LENGTH" => {
            println!("VERIFIER: metadata mismatch: different number of relevant events");
        }
        "DIGEST_MISMATCH_SAME_LENGTH" => {
            println!("VERIFIER: digest mismatch: same length, but real trace changed");
        }
        _ => {
            println!("VERIFIER: unknown status");
        }
    }

    println!("Expected timeline:");
    println!("  {}", case.expected.timeline());
    println!("Observed timeline:");
    println!("  {}", case.observed.timeline());
}

fn write_all_cases_report(cases: &[CompareCase]) {
    let mut report = String::new();

    report.push_str("TimeFence real-ingestion 3-case report\n");
    report.push_str("======================================\n");
    report.push_str("source=strace\n");
    report.push_str("core=timefence-core path dependency\n");
    report.push_str("accumulator=K-Sentry triangular O(1) updater\n\n");

    for case in cases {
        report.push_str(&format!("Case: {}\n", case.name));
        report.push_str(&format!("status={}\n", case.status));
        report.push_str(&format!(
            "expected_raw_syscall_lines_seen={}\n",
            case.expected.raw_syscall_lines_seen
        ));
        report.push_str(&format!(
            "observed_raw_syscall_lines_seen={}\n",
            case.observed.raw_syscall_lines_seen
        ));
        report.push_str(&format!("expected_relevant_events={}\n", case.expected.len()));
        report.push_str(&format!("observed_relevant_events={}\n", case.observed.len()));
        report.push_str(&format!("expected_digest={}\n", case.expected.digest));
        report.push_str(&format!("observed_digest={}\n", case.observed.digest));

        report.push_str("\nExpected timeline:\n");
        for event in &case.expected.events {
            report.push_str(&format!(
                "- {:?} process={} target={}\n",
                event.event.kind,
                event.event.process,
                event.event.target
            ));
        }

        report.push_str("\nObserved timeline:\n");
        for event in &case.observed.events {
            report.push_str(&format!(
                "- {:?} process={} target={}\n",
                event.event.kind,
                event.event.process,
                event.event.target
            ));
        }

        report.push_str("\nExpected one-line timeline:\n");
        report.push_str(&case.expected.timeline());
        report.push('\n');

        report.push_str("\nObserved one-line timeline:\n");
        report.push_str(&case.observed.timeline());
        report.push_str("\n\n");
        report.push_str("--------------------------------------\n\n");
    }

    fs::write("timefence_trace_3case_report.txt", report)
        .expect("failed to write 3-case report");
}

fn main() {
    let q = 7u128;
    let p = 1_000_000_007u128;

    println!("=== TimeFence real-ingestion v2: three-case strace demo ===");
    println!("Using verified-backed core from timefence-core");

    let clean_script =
        "echo secret-token >/tmp/timefence_clean.txt; cat /tmp/timefence_clean.txt; true";

    let clean_observed_script =
        "echo secret-token >/tmp/timefence_clean.txt; cat /tmp/timefence_clean.txt; true";

    let extra_overwrite_script = "echo secret-token >/tmp/timefence_extra.txt; echo tampered-token >/tmp/timefence_extra.txt; cat /tmp/timefence_extra.txt; true";

    let same_length_changed_script =
        "echo tampered-token >/tmp/timefence_observed.txt; cat /tmp/timefence_observed.txt; true";

    let cases = vec![
        build_case(
            "clean_vs_clean",
            clean_script,
            clean_observed_script,
            q,
            p,
        ),
        build_case(
            "clean_vs_extra_overwrite",
            clean_script,
            extra_overwrite_script,
            q,
            p,
        ),
        build_case(
            "clean_vs_same_length_change",
            clean_script,
            same_length_changed_script,
            q,
            p,
        ),
    ];

    for case in &cases {
        print_trace_run(&case.expected, p);
        print_trace_run(&case.observed, p);
        print_case_summary(case);
    }

    write_all_cases_report(&cases);

    println!("\nWrote 3-case report to timefence_trace_3case_report.txt");
}