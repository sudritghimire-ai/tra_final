use std::collections::VecDeque;
use std::convert::TryFrom;
use std::fs;
use std::mem;
use std::thread;
use std::time::Duration;

use aya::{
    include_bytes_aligned,
    maps::ring_buf::RingBuf,
    programs::TracePoint,
    Ebpf,
};

use TraceLock_core::events::{EventKind, TelemetryEvent};
use TraceLock_core::ksentry::KSentry;
use TraceLock_epbf_common::{
    RawKernelEvent, EVENT_CONNECT, EVENT_EXEC, EVENT_OPENAT,
};

#[derive(Debug, Clone)]
struct LiveEventRecord {
    event_type: String,
    pid: u32,
    uid: u32,
    timestamp_ns: u64,
    comm: String,
    target: String,
    field_element: u128,
    digest_after: u128,
}

fn bytes_to_string(bytes: &[u8]) -> String {
    let end = bytes.iter().position(|&b| b == 0).unwrap_or(bytes.len());
    String::from_utf8_lossy(&bytes[..end]).to_string()
}

fn parse_raw_kernel_event(data: &[u8]) -> Option<RawKernelEvent> {
    if data.len() < mem::size_of::<RawKernelEvent>() {
        return None;
    }

    let ptr = data.as_ptr() as *const RawKernelEvent;
    Some(unsafe { std::ptr::read_unaligned(ptr) })
}

fn event_type_name(event_type: u32) -> &'static str {
    match event_type {
        EVENT_EXEC => "Exec",
        EVENT_OPENAT => "OpenFile",
        EVENT_CONNECT => "Connect",
        _ => "Unknown",
    }
}

fn should_keep_event(raw: &RawKernelEvent) -> bool {
    let comm = bytes_to_string(&raw.comm);
    let target = bytes_to_string(&raw.target);

    match raw.event_type {
        EVENT_EXEC => {
            comm == "bash"
                || comm == "cat"
                || comm == "ls"
                || comm == "echo"
                || comm == "whoami"
                || comm == "pwd"
                || comm == "curl"
                || comm == "wget"
                || comm == "nc"
                || comm == "python3"
        }

        EVENT_OPENAT => {
            target.contains("/tmp/TraceLock")
                || target.contains("/etc/hostname")
                || target.contains("/etc/passwd")
        }

        EVENT_CONNECT => true,

        _ => false,
    }
}

fn raw_event_to_telemetry(raw: &RawKernelEvent) -> TelemetryEvent {
    let comm = bytes_to_string(&raw.comm);
    let target_text = bytes_to_string(&raw.target);

    match raw.event_type {
        EVENT_EXEC => {
            let target = format!(
                "exec:pid={}:uid={}:comm={}",
                raw.pid, raw.uid, comm
            );

            TelemetryEvent::new(EventKind::Exec, comm, target, raw.timestamp_ns)
        }

        EVENT_OPENAT => {
            let target = if target_text.is_empty() {
                format!("openat:pid={}:uid={}:path=<unknown>", raw.pid, raw.uid)
            } else {
                target_text
            };

            TelemetryEvent::new(EventKind::OpenFile, comm, target, raw.timestamp_ns)
        }

        EVENT_CONNECT => {
            let target = if target_text.is_empty() {
                format!("connect:pid={}:uid={}:target=<unknown>", raw.pid, raw.uid)
            } else {
                target_text
            };

            TelemetryEvent::new(EventKind::Connect, comm, target, raw.timestamp_ns)
        }

        _ => {
            let target = format!("unknown:pid={}:uid={}", raw.pid, raw.uid);
            TelemetryEvent::new(EventKind::Exec, comm, target, raw.timestamp_ns)
        }
    }
}

fn write_live_report(
    path: &str,
    kept_events: u64,
    skipped_events: u64,
    final_digest: u128,
    first_events: &[LiveEventRecord],
    last_events: &VecDeque<LiveEventRecord>,
) -> std::io::Result<()> {
    let mut report = String::new();

    report.push_str("TraceLock eBPF filtered K-Sentry report\n");
    report.push_str("=======================================\n");
    report.push_str("source=eBPF ringbuf\n");
    report.push_str("tracepoints=syscalls:sys_enter_execve,syscalls:sys_enter_openat,syscalls:sys_enter_connect\n");
    report.push_str("filter=Exec(selected shell/tools) OR OpenFile(/tmp/TraceLock,/etc/hostname,/etc/passwd) OR Connect(any)\n");
    report.push_str("core=TraceLock-core path dependency\n");
    report.push_str("accumulator=K-Sentry triangular O(1) updater\n");
    report.push_str(&format!("kept_events={}\n", kept_events));
    report.push_str(&format!("skipped_events={}\n", skipped_events));
    report.push_str(&format!("final_digest={}\n", final_digest));

    report.push_str("\nFirst kept events:\n");
    for e in first_events {
        report.push_str(&format!(
            "- type={} pid={} uid={} ts={} comm={} target={} x={} digest_after={}\n",
            e.event_type,
            e.pid,
            e.uid,
            e.timestamp_ns,
            e.comm,
            e.target,
            e.field_element,
            e.digest_after
        ));
    }

    report.push_str("\nLast kept events:\n");
    for e in last_events {
        report.push_str(&format!(
            "- type={} pid={} uid={} ts={} comm={} target={} x={} digest_after={}\n",
            e.event_type,
            e.pid,
            e.uid,
            e.timestamp_ns,
            e.comm,
            e.target,
            e.field_element,
            e.digest_after
        ));
    }

    fs::write(path, report)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== TraceLock eBPF ringbuf v5: exec/openat/connect + K-Sentry ===");

    let q = 7u128;
    let p = 1_000_000_007u128;

    let mut ks = KSentry::new(q, p);

    let mut kept_events: u64 = 0;
    let mut skipped_events: u64 = 0;

    let mut first_events: Vec<LiveEventRecord> = Vec::new();
    let mut last_events: VecDeque<LiveEventRecord> = VecDeque::new();

    let mut ebpf = Ebpf::load(include_bytes_aligned!(concat!(
        env!("OUT_DIR"),
        "/TraceLock-epbf"
    )))?;

    let exec_program: &mut TracePoint = ebpf
        .program_mut("TraceLock")
        .unwrap()
        .try_into()?;
    exec_program.load()?;
    exec_program.attach("syscalls", "sys_enter_execve")?;

    let openat_program: &mut TracePoint = ebpf
        .program_mut("TraceLock_openat")
        .unwrap()
        .try_into()?;
    openat_program.load()?;
    openat_program.attach("syscalls", "sys_enter_openat")?;

    let connect_program: &mut TracePoint = ebpf
        .program_mut("TraceLock_connect")
        .unwrap()
        .try_into()?;
    connect_program.load()?;
    connect_program.attach("syscalls", "sys_enter_connect")?;

    let mut ring_buf = RingBuf::try_from(ebpf.map_mut("EVENTS").unwrap())?;

    println!("Attached to:");
    println!("  syscalls:sys_enter_execve");
    println!("  syscalls:sys_enter_openat");
    println!("  syscalls:sys_enter_connect");
    println!();
    println!("Open another WSL terminal and run:");
    println!("  echo secret-token >/tmp/TraceLock_live.txt");
    println!("  cat /tmp/TraceLock_live.txt");
    println!("  cat /etc/hostname");
    println!("  curl -I http://example.com");
    println!();
    println!("Listening. The program stops after 30 kept events.\n");

    while kept_events < 30 {
        while let Some(item) = ring_buf.next() {
            if let Some(raw) = parse_raw_kernel_event(&item) {
                if !should_keep_event(&raw) {
                    skipped_events += 1;
                    continue;
                }

                let telemetry = raw_event_to_telemetry(&raw);
                let x = telemetry.to_field_element(p);

                ks.update(x);
                kept_events += 1;

                let comm = bytes_to_string(&raw.comm);
                let raw_target = bytes_to_string(&raw.target);
                let target = if raw_target.is_empty() {
                    "<empty>".to_string()
                } else {
                    raw_target
                };

                let event_type = event_type_name(raw.event_type).to_string();

                let record = LiveEventRecord {
                    event_type: event_type.clone(),
                    pid: raw.pid,
                    uid: raw.uid,
                    timestamp_ns: raw.timestamp_ns,
                    comm: comm.clone(),
                    target: target.clone(),
                    field_element: x,
                    digest_after: ks.digest(),
                };

                if first_events.len() < 5 {
                    first_events.push(record.clone());
                }

                if last_events.len() == 5 {
                    last_events.pop_front();
                }

                last_events.push_back(record);

                println!(
                    "{} kept: pid={} uid={} ts={} comm={} target={}",
                    event_type, raw.pid, raw.uid, raw.timestamp_ns, comm, target
                );

                println!("  telemetry: {}", telemetry.short_label());
                println!("  field element x={}", x);
                println!(
                    "  live checkpoint: kept_events={} digest={}",
                    kept_events,
                    ks.digest()
                );
                println!("  skipped_events={}", skipped_events);
                println!();

                if kept_events >= 30 {
                    break;
                }
            }
        }

        thread::sleep(Duration::from_millis(100));
    }

    let report_path = "TraceLock_ebpf_filtered_report.txt";

    write_live_report(
        report_path,
        kept_events,
        skipped_events,
        ks.digest(),
        &first_events,
        &last_events,
    )?;

    println!("Stopped after {} kept events.", kept_events);
    println!("Skipped events: {}", skipped_events);
    println!("Final filtered live digest: {}", ks.digest());
    println!("Wrote filtered eBPF report to {}", report_path);

    Ok(())
}