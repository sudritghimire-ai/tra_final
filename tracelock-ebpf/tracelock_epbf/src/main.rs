cd ~/k-sentry/TraceLock-epbf

cat > TraceLock_epbf_ebpf/src/main.rs <<'EOF'
#![no_std]
#![no_main]

use aya_ebpf::{
    helpers::{
        bpf_get_current_comm, bpf_get_current_pid_tgid, bpf_get_current_uid_gid,
        bpf_ktime_get_ns, bpf_probe_read_user, bpf_probe_read_user_str_bytes,
    },
    macros::{map, tracepoint},
    maps::{Array, RingBuf},
    programs::TracePointContext,
};

use TraceLock_epbf_common::{
    RawKernelEvent, DROP_COUNTER_KEY, EVENT_CONNECT, EVENT_EXEC, EVENT_OPENAT,
};

#[map]
static EVENTS: RingBuf = RingBuf::with_byte_size(16384, 0);

#[map]
static RINGBUF_OUTPUT_FAILURES: Array<u64> = Array::with_max_entries(1, 0);

#[repr(C)]
#[derive(Clone, Copy)]
struct SockAddrIn {
    sin_family: u16,
    sin_port: u16,
    sin_addr: u32,
    sin_zero: [u8; 8],
}

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

fn count_ringbuf_output_failure() {
    unsafe {
        if let Some(counter) = RINGBUF_OUTPUT_FAILURES.get_ptr_mut(DROP_COUNTER_KEY) {
            *counter += 1;
        }
    }
}

fn emit_event(event: &RawKernelEvent) -> Result<u32, u32> {
    match EVENTS.output(event, 0) {
        Ok(_) => Ok(0),
        Err(_) => {
            count_ringbuf_output_failure();
            Err(1)
        }
    }
}

fn write_bytes(dst: &mut [u8; 128], src: &[u8]) {
    let mut i = 0usize;
    while i < src.len() && i < dst.len() {
        dst[i] = src[i];
        i += 1;
    }
}

fn write_u16_decimal(dst: &mut [u8; 128], mut pos: usize, mut n: u16) -> usize {
    let mut buf = [0u8; 5];
    let mut len = 0usize;

    if n == 0 {
        if pos < dst.len() {
            dst[pos] = b'0';
            return pos + 1;
        }
        return pos;
    }

    while n > 0 && len < buf.len() {
        buf[len] = b'0' + (n % 10) as u8;
        n /= 10;
        len += 1;
    }

    while len > 0 && pos < dst.len() {
        len -= 1;
        dst[pos] = buf[len];
        pos += 1;
    }

    pos
}

fn write_u8_decimal(dst: &mut [u8; 128], mut pos: usize, mut n: u8) -> usize {
    let mut buf = [0u8; 3];
    let mut len = 0usize;

    if n == 0 {
        if pos < dst.len() {
            dst[pos] = b'0';
            return pos + 1;
        }
        return pos;
    }

    while n > 0 && len < buf.len() {
        buf[len] = b'0' + (n % 10) as u8;
        n /= 10;
        len += 1;
    }

    while len > 0 && pos < dst.len() {
        len -= 1;
        dst[pos] = buf[len];
        pos += 1;
    }

    pos
}

fn write_ipv4_port(dst: &mut [u8; 128], addr_be: u32, port_be: u16) {
    let b1 = ((addr_be >> 0) & 0xff) as u8;
    let b2 = ((addr_be >> 8) & 0xff) as u8;
    let b3 = ((addr_be >> 16) & 0xff) as u8;
    let b4 = ((addr_be >> 24) & 0xff) as u8;

    let port = u16::from_be(port_be);

    let mut pos = 0usize;

    pos = write_u8_decimal(dst, pos, b1);
    if pos < dst.len() {
        dst[pos] = b'.';
        pos += 1;
    }

    pos = write_u8_decimal(dst, pos, b2);
    if pos < dst.len() {
        dst[pos] = b'.';
        pos += 1;
    }

    pos = write_u8_decimal(dst, pos, b3);
    if pos < dst.len() {
        dst[pos] = b'.';
        pos += 1;
    }

    pos = write_u8_decimal(dst, pos, b4);
    if pos < dst.len() {
        dst[pos] = b':';
        pos += 1;
    }

    let _ = write_u16_decimal(dst, pos, port);
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
    emit_event(&event)
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

    let filename_ptr: u64 = unsafe { ctx.read_at(24).map_err(|_| 1u32)? };

    if filename_ptr != 0 {
        let ptr = filename_ptr as *const u8;
        let _ = unsafe { bpf_probe_read_user_str_bytes(ptr, &mut event.target) };
    }

    emit_event(&event)
}

#[tracepoint]
pub fn TraceLock_connect(ctx: TracePointContext) -> u32 {
    match try_connect(ctx) {
        Ok(ret) => ret,
        Err(ret) => ret,
    }
}

fn try_connect(ctx: TracePointContext) -> Result<u32, u32> {
    let mut event = fill_common(EVENT_CONNECT);

    // syscalls:sys_enter_connect on x86_64:
    // fd at offset 16, sockaddr pointer at offset 24, addrlen at offset 32.
    let sockaddr_ptr: u64 = unsafe { ctx.read_at(24).map_err(|_| 1u32)? };

    if sockaddr_ptr != 0 {
        let sockaddr = unsafe { bpf_probe_read_user(sockaddr_ptr as *const SockAddrIn) };

        if let Ok(sa) = sockaddr {
            if sa.sin_family == 2 {
                write_ipv4_port(&mut event.target, sa.sin_addr, sa.sin_port);
            } else {
                write_bytes(&mut event.target, b"socket_connect_non_ipv4\0");
            }
        } else {
            write_bytes(&mut event.target, b"socket_connect_unreadable\0");
        }
    } else {
        write_bytes(&mut event.target, b"socket_connect_null\0");
    }

    emit_event(&event)
}

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}
EOF