//! `sha256sum` with no operand, as a WASI preview1 core module with exactly four imports
//! (`fd_read`, `fd_write`, `fd_close`, `proc_exit`) and no libc.
//!
//! It follows the call sequence of silmaril's reference program
//! `Silmaril.Apps.Sha256sum.Sys.refMachine`: read descriptor 0 in requests of 32768 bytes
//! until a read returns no bytes; write `hex(SHA-256(input)) ++ "  -\n"` to descriptor 1,
//! retrying partial writes; close descriptors 0, 1 and 2; exit 0. Every iovec list has one
//! entry. An error answer traps (the reference program is stuck there too).
#![no_std]

#[link(wasm_import_module = "wasi_snapshot_preview1")]
unsafe extern "C" {
    fn fd_read(fd: u32, iovs: *const IoVec, n: u32, nread: *mut u32) -> u32;
    fn fd_write(fd: u32, iovs: *const IoVec, n: u32, nwritten: *mut u32) -> u32;
    fn fd_close(fd: u32) -> u32;
    fn proc_exit(code: u32) -> !;
}

#[repr(C)]
struct IoVec {
    buf: *const u8,
    len: u32,
}

const CHUNK: usize = 32768;
static mut BUF: [u8; CHUNK] = [0; CHUNK];

const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

struct Sha {
    h: [u32; 8],
    block: [u8; 64],
    fill: usize,
    len: u64,
}

impl Sha {
    fn new() -> Sha {
        Sha {
            h: [
                0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
                0x5be0cd19,
            ],
            block: [0; 64],
            fill: 0,
            len: 0,
        }
    }

    fn compress(&mut self) {
        let mut w = [0u32; 64];
        for i in 0..16 {
            w[i] = u32::from_be_bytes([
                self.block[4 * i],
                self.block[4 * i + 1],
                self.block[4 * i + 2],
                self.block[4 * i + 3],
            ]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16].wrapping_add(s0).wrapping_add(w[i - 7]).wrapping_add(s1);
        }
        let mut v = self.h;
        for i in 0..64 {
            let s1 = v[4].rotate_right(6) ^ v[4].rotate_right(11) ^ v[4].rotate_right(25);
            let ch = (v[4] & v[5]) ^ (!v[4] & v[6]);
            let t1 = v[7].wrapping_add(s1).wrapping_add(ch).wrapping_add(K[i]).wrapping_add(w[i]);
            let s0 = v[0].rotate_right(2) ^ v[0].rotate_right(13) ^ v[0].rotate_right(22);
            let maj = (v[0] & v[1]) ^ (v[0] & v[2]) ^ (v[1] & v[2]);
            let t2 = s0.wrapping_add(maj);
            v = [t1.wrapping_add(t2), v[0], v[1], v[2], v[3].wrapping_add(t1), v[4], v[5], v[6]];
        }
        for i in 0..8 {
            self.h[i] = self.h[i].wrapping_add(v[i]);
        }
    }

    fn update(&mut self, data: &[u8]) {
        for &b in data {
            self.block[self.fill] = b;
            self.fill += 1;
            if self.fill == 64 {
                self.compress();
                self.fill = 0;
            }
        }
        self.len = self.len.wrapping_add(data.len() as u64);
    }

    fn finish(mut self) -> [u8; 32] {
        let bits = self.len.wrapping_mul(8);
        self.update(&[0x80]);
        while self.fill != 56 {
            self.update(&[0]);
        }
        let len = bits.to_be_bytes();
        for b in len {
            self.block[self.fill] = b;
            self.fill += 1;
        }
        self.compress();
        let mut out = [0u8; 32];
        for i in 0..8 {
            out[4 * i..4 * i + 4].copy_from_slice(&self.h[i].to_be_bytes());
        }
        out
    }
}

fn fail() -> ! {
    core::arch::wasm32::unreachable()
}

#[unsafe(no_mangle)]
pub extern "C" fn _start() {
    let mut sha = Sha::new();
    let buf = &raw mut BUF as *mut u8;
    loop {
        let iov = IoVec { buf, len: CHUNK as u32 };
        let mut n = 0u32;
        if unsafe { fd_read(0, &iov, 1, &mut n) } != 0 {
            fail();
        }
        if n == 0 {
            break;
        }
        sha.update(unsafe { core::slice::from_raw_parts(buf, n as usize) });
    }
    let digest = sha.finish();
    let hex = b"0123456789abcdef";
    let mut rec = [0u8; 68];
    for i in 0..32 {
        rec[2 * i] = hex[(digest[i] >> 4) as usize];
        rec[2 * i + 1] = hex[(digest[i] & 15) as usize];
    }
    rec[64..].copy_from_slice(b"  -\n");
    let mut off = 0usize;
    while off < rec.len() {
        let iov = IoVec { buf: rec[off..].as_ptr(), len: (rec.len() - off) as u32 };
        let mut k = 0u32;
        if unsafe { fd_write(1, &iov, 1, &mut k) } != 0 || k == 0 {
            fail();
        }
        off += k as usize;
    }
    for fd in 0..3 {
        if unsafe { fd_close(fd) } != 0 {
            fail();
        }
    }
    unsafe { proc_exit(0) }
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    fail()
}
