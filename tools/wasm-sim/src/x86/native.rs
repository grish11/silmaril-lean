//! Native oracle: execute x86-64 bytes on this CPU from a given register/flag state and
//! capture the resulting state.
//!
//! A stub (below) is copied into an RWX page. It saves the host's callee-saved registers and
//! rsp, loads rflags and all 16 GPRs (including rsp) from a `State`, falls into a slot of
//! nops ending with the instruction under test, and then lands either at `fall` (the address
//! right after the slot) or at `taken` (a second landing pad, the target of any relative
//! branch the test encodes). Both pads store all GPRs and rflags back and record which pad
//! was reached as `rip`. Everything inside the page is rip-relative, so the stub is position
//! independent. Simulator and CPU then run at the *same* addresses (the simulator reads real
//! memory through `harness::RawMem`), so pointers, return addresses and rip compare directly.

use std::arch::global_asm;

/// Register file as the stub sees it: 16 GPRs (hardware order), rflags, rip (output).
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct State {
    pub r: [u64; 16],
    pub flags: u64,
    pub rip: u64,
}

global_asm!(
    r#"
    .text
    .p2align 4
    .globl wsim_stub_start
wsim_stub_start:
    push rbx
    push rbp
    push r12
    push r13
    push r14
    push r15
    mov [rip + wsim_st_ptr], rdi
    mov [rip + wsim_host_rsp], rsp
    push qword ptr [rdi + 128]
    popfq
    mov rax, [rdi + 0]
    mov rcx, [rdi + 8]
    mov rdx, [rdi + 16]
    mov rbx, [rdi + 24]
    mov rsp, [rdi + 32]
    mov rbp, [rdi + 40]
    mov rsi, [rdi + 48]
    mov r8,  [rdi + 64]
    mov r9,  [rdi + 72]
    mov r10, [rdi + 80]
    mov r11, [rdi + 88]
    mov r12, [rdi + 96]
    mov r13, [rdi + 104]
    mov r14, [rdi + 112]
    mov r15, [rdi + 120]
    mov rdi, [rdi + 56]
    .globl wsim_slot
wsim_slot:
    .fill 64, 1, 0x90
    .globl wsim_fall
wsim_fall:
    mov [rip + wsim_scratch], rax
    lea rax, [rip + wsim_fall]
    jmp wsim_save
    .globl wsim_taken
wsim_taken:
    mov [rip + wsim_scratch], rax
    lea rax, [rip + wsim_taken]
wsim_save:
    mov [rip + wsim_where], rax
    mov rax, [rip + wsim_st_ptr]
    mov [rax + 8], rcx
    mov [rax + 16], rdx
    mov [rax + 24], rbx
    mov [rax + 32], rsp
    mov [rax + 40], rbp
    mov [rax + 48], rsi
    mov [rax + 56], rdi
    mov [rax + 64], r8
    mov [rax + 72], r9
    mov [rax + 80], r10
    mov [rax + 88], r11
    mov [rax + 96], r12
    mov [rax + 104], r13
    mov [rax + 112], r14
    mov [rax + 120], r15
    mov rsp, [rip + wsim_host_rsp]
    pushfq
    pop rcx
    mov [rax + 128], rcx
    mov rcx, [rip + wsim_scratch]
    mov [rax + 0], rcx
    mov rcx, [rip + wsim_where]
    mov [rax + 136], rcx
    cld
    pop r15
    pop r14
    pop r13
    pop r12
    pop rbp
    pop rbx
    ret
    .p2align 3
wsim_st_ptr: .quad 0
wsim_host_rsp: .quad 0
wsim_scratch: .quad 0
wsim_where: .quad 0
    .globl wsim_stub_end
wsim_stub_end:
"#
);

unsafe extern "C" {
    static wsim_stub_start: u8;
    static wsim_slot: u8;
    static wsim_fall: u8;
    static wsim_taken: u8;
    static wsim_stub_end: u8;
}

pub const SLOT_LEN: usize = 64;
/// Offset in the page where function code (for whole-function tests) is placed.
pub const CODE_OFF: usize = 0x1000;
pub const PAGE_LEN: usize = 0x10000;

/// The RWX page with the stub copied in.
pub struct Native {
    pub page: *mut u8,
    pub slot: u64,
    pub fall: u64,
    pub taken: u64,
}

fn addr(s: &u8) -> usize {
    s as *const u8 as usize
}

pub fn mmap(len: usize, exec: bool) -> *mut u8 {
    let prot = libc::PROT_READ | libc::PROT_WRITE | if exec { libc::PROT_EXEC } else { 0 };
    // SAFETY: anonymous private mapping.
    let p = unsafe {
        libc::mmap(
            std::ptr::null_mut(),
            len,
            prot,
            libc::MAP_PRIVATE | libc::MAP_ANONYMOUS,
            -1,
            0,
        )
    };
    assert!(p != libc::MAP_FAILED, "mmap failed");
    p as *mut u8
}

impl Default for Native {
    fn default() -> Self {
        Self::new()
    }
}

impl Native {
    pub fn new() -> Native {
        let page = mmap(PAGE_LEN, true);
        // SAFETY: reading our own static code bytes; the page is fresh and large enough.
        unsafe {
            let start = addr(&wsim_stub_start);
            let len = addr(&wsim_stub_end) - start;
            assert!(len < CODE_OFF);
            std::ptr::copy_nonoverlapping(start as *const u8, page, len);
            let base = page as u64;
            Native {
                page,
                slot: base + (addr(&wsim_slot) - start) as u64,
                fall: base + (addr(&wsim_fall) - start) as u64,
                taken: base + (addr(&wsim_taken) - start) as u64,
            }
        }
    }

    /// Place `insn` at the end of the slot (preceded by nops); returns its address.
    pub fn place(&mut self, insn: &[u8]) -> u64 {
        assert!(insn.len() <= SLOT_LEN);
        let off = (self.slot - self.page as u64) as usize;
        // SAFETY: inside the page.
        unsafe {
            std::ptr::write_bytes(self.page.add(off), 0x90, SLOT_LEN);
            std::ptr::copy_nonoverlapping(
                insn.as_ptr(),
                self.page.add(off + SLOT_LEN - insn.len()),
                insn.len(),
            );
        }
        self.fall - insn.len() as u64
    }

    /// Copy function code to CODE_OFF; returns its address.
    pub fn place_code(&mut self, code: &[u8]) -> u64 {
        assert!(code.len() <= PAGE_LEN - CODE_OFF);
        // SAFETY: inside the page.
        unsafe {
            std::ptr::copy_nonoverlapping(code.as_ptr(), self.page.add(CODE_OFF), code.len())
        };
        self.page as u64 + CODE_OFF as u64
    }

    /// Run the slot natively from `st`.
    ///
    /// # Safety
    ///
    /// The caller guarantees that the code under test only touches memory it owns and ends at
    /// `fall` or `taken`.
    pub unsafe fn run(&mut self, st: &State) -> State {
        let mut s = *st;
        s.flags = (s.flags & 0x8d5) | 0x202;
        let f: extern "C" fn(*mut State) = unsafe { std::mem::transmute(self.page) };
        f(&mut s);
        s
    }

    pub fn range(&self) -> (u64, u64) {
        (self.page as u64, self.page as u64 + PAGE_LEN as u64)
    }
}
