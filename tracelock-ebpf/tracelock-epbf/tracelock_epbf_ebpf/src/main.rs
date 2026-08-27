#![no_std]
#![no_main]

use aya_ebpf::{
    helpers::{
        bpf_get_current_comm, bpf_get_current_pid_tgid, bpf_get_current_uid_gid,
        bpf_ktime_get_ns, bpf_probe_read_user_str_bytes,
    },
    macros::{map, tracepoint},
    maps::RingBuf,
    programs::TracePointContext,
};

use TraceLock_epbf_common::{
    RawKernelEvent, EVENT_CONNECT, EVENT_EXEC, EVENT_OPENAT,
};

#[map]
static EVENTS: RingBuf = RingBuf::with_byte_size(16384, 0);

fn fill_common(event_type: u32) -> RawKernelEvent {
    let pid_tgid = bpf_get_current_pid_tgid();
    let uid_gid = bpf_get_current_uid_gid();
    let timestamp_ns = unsafe { bpf_ktime_get_ns() };

    let mut event = RawKernelEvent {
        event_type,
        pid: (pid_tgid >> 32) as u32,
        uid: uid_gid as u32,
        timestamp_ns,
        comm: [0u8; 16],
        target: [0u8; 128],
    };

    if let Ok(comm) = bpf_get_current_comm() {
        event.comm = comm;
    }

    event
}

#[tracepoint]
pub fn TraceLock(ctx: TracePointContext) -> u32 {
    match try_execve(ctx) {
        Ok(ret) => ret,
        Err(ret) => ret,
    }
}

fn try_execve(_ctx: TracePointContext) -> Result<u32, u32> {
    let event = fill_common(EVENT_EXEC);
    EVENTS.output(&event, 0).map_err(|_| 1u32)?;
    Ok(0)
}

#[tracepoint]
pub fn TraceLock_openat(ctx: TracePointContext) -> u32 {
    match try_openat(ctx) {
        Ok(ret) => ret,
        Err(ret) => ret,
    }
}

fn try_openat(ctx: TracePointContext) -> Result<u32, u32> {
    let mut event = fill_common(EVENT_OPENAT);

    // syscalls:sys_enter_openat filename pointer offset on this WSL/kernel setup.
    let filename_ptr: u64 = unsafe { ctx.read_at(24).map_err(|_| 1u32)? };

    if filename_ptr != 0 {
        let ptr = filename_ptr as *const u8;
        let _ = unsafe { bpf_probe_read_user_str_bytes(ptr, &mut event.target) };
    }

    EVENTS.output(&event, 0).map_err(|_| 1u32)?;
    Ok(0)
}

#[tracepoint]
pub fn TraceLock_connect(ctx: TracePointContext) -> u32 {
    match try_connect(ctx) {
        Ok(ret) => ret,
        Err(ret) => ret,
    }
}

fn try_connect(_ctx: TracePointContext) -> Result<u32, u32> {
    let mut event = fill_common(EVENT_CONNECT);

    // Minimal v0: record that a connect syscall happened.
    // Later we can parse sockaddr for IP/port.
    let label = b"socket_connect\0";

    let mut i = 0;
    while i < label.len() && i < event.target.len() {
        event.target[i] = label[i];
        i += 1;
    }

    EVENTS.output(&event, 0).map_err(|_| 1u32)?;
    Ok(0)
}

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}