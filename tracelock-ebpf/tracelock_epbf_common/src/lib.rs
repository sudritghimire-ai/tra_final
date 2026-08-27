#![no_std]

pub const EVENT_EXEC: u32 = 1;
pub const EVENT_OPENAT: u32 = 2;
pub const EVENT_CONNECT: u32 = 3;

#[repr(C)]
#[derive(Clone, Copy)]
pub struct RawKernelEvent {
    pub event_type: u32,
    pub pid: u32,
    pub uid: u32,
    pub timestamp_ns: u64,
    pub comm: [u8; 16],
    pub target: [u8; 128],
}