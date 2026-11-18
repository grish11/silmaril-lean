//! Differential tests of the x86 simulators against this CPU, lockstep tests between
//! simulators, and benchmarks.
//!
//! * `difftest-insn`: random instances of every implemented instruction form (assembled by
//!   GNU as from Intel-syntax text, branches as raw bytes), executed natively by
//!   `native::Native` and by the simulator (one `step`) from the same registers, flags and
//!   memory, at the same addresses. Compared: 16 GPRs, rip, CF PF AF ZF SF OF, and a 16 KiB
//!   data buffer. Locations the simulator leaves undefined are detected by running the
//!   simulator twice (`nd.undef` answering all-zeros, then all-ones) and excluded.
//! * `difftest-fn`: the functions of `tests/funcs.S` on random arguments; the native slot
//!   instruction is `call fn`, the simulator steps until rip returns to the slot's end.
//! * `lockstep`: G vs M (and P-calls vs P-mem) after every instruction.

use super::native::{self, Native, State};
use super::{NAMES, NLOCS, RIP};
use crate::harness::{self, Host, PageMem, RawMem, Sim, Undef};
use anyhow::{Context, Result, bail};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

pub struct Rng(pub u64);
impl Rng {
    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }
    pub fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }
    pub fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len() as u64) as usize]
    }
    /// interesting 64-bit values
    pub fn val(&mut self) -> u64 {
        match self.below(10) {
            0 => *self.pick(&[
                0,
                1,
                2,
                u64::MAX,
                0x7fff_ffff_ffff_ffff,
                0x8000_0000_0000_0000,
                0xffff_ffff,
                0x8000_0000,
                0x7fff_ffff,
                0x80,
                0x7f,
                0xff,
            ]),
            1 => self.below(16),
            2 => self.next_u64() & 0xffff_ffff,
            3 => (self.next_u64() as i8) as u64,
            4 => (self.next_u64() as i32) as u64,
            _ => self.next_u64(),
        }
    }
}

const R64: [&str; 16] = [
    "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13",
    "r14", "r15",
];
const R32: [&str; 16] = [
    "eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi", "r8d", "r9d", "r10d", "r11d", "r12d",
    "r13d", "r14d", "r15d",
];
const R16: [&str; 16] = [
    "ax", "cx", "dx", "bx", "sp", "bp", "si", "di", "r8w", "r9w", "r10w", "r11w", "r12w", "r13w",
    "r14w", "r15w",
];
const R8: [&str; 16] = [
    "al", "cl", "dl", "bl", "spl", "bpl", "sil", "dil", "r8b", "r9b", "r10b", "r11b", "r12b",
    "r13b", "r14b", "r15b",
];
const R8L: [&str; 8] = ["al", "cl", "dl", "bl", "ah", "ch", "dh", "bh"];
const CC: [&str; 16] = [
    "o", "no", "b", "ae", "e", "ne", "be", "a", "s", "ns", "p", "np", "l", "ge", "le", "g",
];
const ALU: [&str; 8] = ["add", "or", "adc", "sbb", "and", "sub", "xor", "cmp"];

pub const DATA_LEN: usize = 0x4000;
pub const RSP_OFF: u64 = 0x2000;

/// One generated test case.
#[derive(Clone)]
struct Case {
    form: &'static str,
    asm: String,
    st: State,
    /// 64-bit values to write into the data buffer (offset, value)
    patch: Vec<(u64, u64)>,
}

struct Gen<'a> {
    rng: &'a mut Rng,
    data: u64,
    st: State,
    patch: Vec<(u64, u64)>,
    /// registers already given a role (address registers)
    fixed: Vec<usize>,
}

impl Gen<'_> {
    /// a random register (not rsp, not already fixed)
    fn reg(&mut self) -> usize {
        loop {
            let r = self.rng.below(16) as usize;
            if r != 4 && !self.fixed.contains(&r) {
                return r;
            }
        }
    }
    /// a free register for a value operand (may coincide with others; not rsp)
    fn vreg(&mut self) -> usize {
        loop {
            let r = self.rng.below(16) as usize;
            if r != 4 {
                return r;
            }
        }
    }
    /// a memory operand addressing the data buffer
    fn mem(&mut self, size: &str) -> String {
        let target = self.data + 0x800 + self.rng.below(0x2000);
        let b = if self.rng.below(6) == 0 {
            4
        } else {
            self.reg()
        };
        self.fixed.push(b);
        let use_idx = self.rng.below(2) == 0;
        let mut idxv = 0u64;
        let mut txt = format!("{size} ptr [{}", R64[b]);
        if use_idx {
            let i = self.reg();
            self.fixed.push(i);
            let s = self.rng.below(4);
            let v = self.rng.below(0x40);
            self.st.r[i] = v;
            idxv = v << s;
            txt += &format!("+{}*{}", R64[i], 1 << s);
        }
        let disp: i64 = match self.rng.below(3) {
            0 => 0,
            1 => self.rng.below(256) as i64 - 128,
            _ => self.rng.below(0x1000) as i64 - 0x800,
        };
        if b == 4 {
            // rsp is fixed: choose disp to land in the buffer
            let d = target.wrapping_sub(self.st.r[4]).wrapping_sub(idxv) as i64;
            txt += &format!("{:+}]", d);
        } else {
            self.st.r[b] = target.wrapping_sub(idxv).wrapping_sub(disp as u64);
            if disp != 0 {
                txt += &format!("{:+}", disp);
            }
            txt += "]";
        }
        txt
    }
    fn imm32(&mut self) -> i64 {
        (self.rng.val() as i32) as i64
    }
    fn imm8(&mut self) -> i64 {
        (self.rng.val() as i8) as i64
    }
}

fn gen_case(rng: &mut Rng, data: u64, rel_taken: i64, taken: u64, form: usize) -> Case {
    let mut st = State::default();
    for r in st.r.iter_mut() {
        *r = rng.val();
    }
    st.r[4] = data + RSP_OFF;
    st.flags = rng.next_u64() & 0x8d5;
    let mut g = Gen {
        rng,
        data,
        st,
        patch: vec![],
        fixed: vec![4],
    };
    let rel8 = |op: u8| format!(".byte {:#x}, {:#x}", op, rel_taken as u8);
    let rel32 = |ops: &str| {
        let b = (rel_taken as i32).to_le_bytes();
        format!(
            ".byte {ops}, {:#x}, {:#x}, {:#x}, {:#x}",
            b[0], b[1], b[2], b[3]
        )
    };
    let (name, asm): (&'static str, String) = match form {
        0 => {
            let o = g.rng.pick(&ALU);
            let (a, b) = (g.vreg(), g.vreg());
            ("alu r64,r64", format!("{o} {}, {}", R64[a], R64[b]))
        }
        1 => {
            let o = g.rng.pick(&ALU);
            let (a, b) = (g.vreg(), g.vreg());
            ("alu r32,r32", format!("{o} {}, {}", R32[a], R32[b]))
        }
        2 => {
            let o = g.rng.pick(&ALU);
            let (a, b) = (g.vreg(), g.vreg());
            if g.rng.below(2) == 0 {
                ("alu r8,r8", format!("{o} {}, {}", R8[a], R8[b]))
            } else {
                (
                    "alu r8,r8 (ah..)",
                    format!("{o} {}, {}", R8L[a & 7], R8L[b & 7]),
                )
            }
        }
        3 => {
            let o = g.rng.pick(&ALU);
            let a = g.vreg();
            let i = g.imm32();
            ("alu r64,imm32", format!("{o} {}, {i}", R64[a]))
        }
        4 => {
            let o = g.rng.pick(&ALU);
            let a = g.vreg();
            let i = g.imm8();
            ("alu r64,imm8", format!("{o} {}, {i}", R64[a]))
        }
        5 => {
            let o = g.rng.pick(&ALU);
            let a = g.vreg();
            let i = g.imm32();
            ("alu r32,imm", format!("{o} {}, {i}", R32[a]))
        }
        6 => {
            let o = g.rng.pick(&ALU);
            let a = g.vreg();
            let i = g.imm8() as u8;
            ("alu r8,imm", format!("{o} {}, {i}", R8[a]))
        }
        7 => {
            let o = g.rng.pick(&ALU);
            let m = g.mem("qword");
            let a = g.vreg();
            ("alu r64,m64", format!("{o} {}, {m}", R64[a]))
        }
        8 => {
            let o = g.rng.pick(&ALU);
            let m = g.mem("qword");
            let a = g.vreg();
            ("alu m64,r64", format!("{o} {m}, {}", R64[a]))
        }
        9 => {
            let o = g.rng.pick(&ALU);
            let m = g.mem("qword");
            let i = g.imm32();
            ("alu m64,imm", format!("{o} {m}, {i}"))
        }
        10 => {
            let o = g.rng.pick(&ALU);
            let m = g.mem("dword");
            let a = g.vreg();
            ("alu m32,r32", format!("{o} {m}, {}", R32[a]))
        }
        11 => {
            let o = g.rng.pick(&ALU);
            let m = g.mem("byte");
            let i = g.imm8() as u8;
            ("alu m8,imm", format!("{o} {m}, {i}"))
        }
        12 => {
            let (a, b) = (g.vreg(), g.vreg());
            ("test r64,r64", format!("test {}, {}", R64[a], R64[b]))
        }
        13 => {
            let a = g.vreg();
            let i = g.imm32();
            ("test r32,imm", format!("test {}, {i}", R32[a]))
        }
        14 => {
            let m = g.mem("qword");
            let a = g.vreg();
            ("test m64,r64", format!("test {m}, {}", R64[a]))
        }
        15 => {
            let (a, b) = (g.vreg(), g.vreg());
            ("mov r64,r64", format!("mov {}, {}", R64[a], R64[b]))
        }
        16 => {
            let (a, b) = (g.vreg(), g.vreg());
            ("mov r32,r32", format!("mov {}, {}", R32[a], R32[b]))
        }
        17 => {
            let (a, b) = (g.vreg(), g.vreg());
            ("mov r8,r8", format!("mov {}, {}", R8L[a & 7], R8L[b & 7]))
        }
        18 => {
            let a = g.vreg();
            let v = g.rng.next_u64();
            ("movabs r64,imm64", format!("movabs {}, {v}", R64[a]))
        }
        19 => {
            let a = g.vreg();
            let v = g.rng.val() as u32;
            ("mov r32,imm32", format!("mov {}, {v}", R32[a]))
        }
        20 => {
            let a = g.vreg();
            let v = g.imm32();
            ("mov r64,simm32", format!("mov {}, {v}", R64[a]))
        }
        21 => {
            let m = g.mem("qword");
            let a = g.vreg();
            ("mov r64,m64", format!("mov {}, {m}", R64[a]))
        }
        22 => {
            let m = g.mem("qword");
            let a = g.vreg();
            ("mov m64,r64", format!("mov {m}, {}", R64[a]))
        }
        23 => {
            let m = g.mem("dword");
            let a = g.vreg();
            ("mov r32,m32", format!("mov {}, {m}", R32[a]))
        }
        24 => {
            let m = g.mem("byte");
            let a = g.vreg();
            ("mov m8,r8", format!("mov {m}, {}", R8[a]))
        }
        25 => {
            let m = g.mem("qword");
            let v = g.imm32();
            ("mov m64,imm", format!("mov {m}, {v}"))
        }
        26 => {
            let m = g.mem("byte");
            let v = g.imm8() as u8;
            ("mov m8,imm", format!("mov {m}, {v}"))
        }
        27 => {
            let a = g.vreg();
            let v = g.imm8() as u8;
            ("mov r8,imm8", format!("mov {}, {v}", R8L[a & 7]))
        }
        28 => {
            let m = g.mem("qword");
            let a = g.vreg();
            ("lea r64", format!("lea {}, {}", R64[a], &m[10..]))
        }
        29 => {
            let m = g.mem("qword");
            let a = g.vreg();
            ("lea r32", format!("lea {}, {}", R32[a], &m[10..]))
        }
        30 => {
            let a = g.vreg();
            let d = g.imm32();
            ("lea rip", format!("lea {}, [rip{:+}]", R64[a], d))
        }
        31 => {
            let (a, b) = (g.vreg(), g.vreg());
            ("movzx r32,r8", format!("movzx {}, {}", R32[a], R8[b]))
        }
        32 => {
            let m = g.mem("byte");
            let a = g.vreg();
            ("movzx r64,m8", format!("movzx {}, {m}", R64[a]))
        }
        33 => {
            let m = g.mem("word");
            let a = g.vreg();
            ("movzx r32,m16", format!("movzx {}, {m}", R32[a]))
        }
        34 => {
            let (a, b) = (g.vreg(), g.vreg());
            ("movsx r64,r8", format!("movsx {}, {}", R64[a], R8[b]))
        }
        35 => {
            let (a, b) = (g.vreg(), g.vreg());
            ("movsx r64,r16", format!("movsx {}, {}", R64[a], R16[b]))
        }
        36 => {
            let m = g.mem("word");
            let a = g.vreg();
            ("movsx r32,m16", format!("movsx {}, {m}", R32[a]))
        }
        37 => {
            let (a, b) = (g.vreg(), g.vreg());
            ("movsxd r64,r32", format!("movsxd {}, {}", R64[a], R32[b]))
        }
        38 => {
            let o = g.rng.pick(&["inc", "dec", "neg", "not"]);
            let a = g.vreg();
            ("unary r64", format!("{o} {}", R64[a]))
        }
        39 => {
            let o = g.rng.pick(&["inc", "dec", "neg", "not"]);
            let a = g.vreg();
            ("unary r32", format!("{o} {}", R32[a]))
        }
        40 => {
            let o = g.rng.pick(&["inc", "dec", "neg", "not"]);
            let a = g.vreg();
            ("unary r8", format!("{o} {}", R8[a]))
        }
        41 => {
            let o = g.rng.pick(&["inc", "dec", "neg", "not"]);
            let m = g.mem("qword");
            ("unary m64", format!("{o} {m}"))
        }
        42 => {
            let o = g.rng.pick(&["shl", "shr", "sar"]);
            let a = g.vreg();
            let n = g.rng.below(70);
            ("shift r64,imm", format!("{o} {}, {n}", R64[a]))
        }
        43 => {
            let o = g.rng.pick(&["shl", "shr", "sar"]);
            let a = g.vreg();
            let n = g.rng.below(40);
            ("shift r32,imm", format!("{o} {}, {n}", R32[a]))
        }
        44 => {
            let o = g.rng.pick(&["shl", "shr", "sar"]);
            let a = g.vreg();
            (
                "shift r64,1",
                format!(
                    ".byte 0x48+{}, 0xd1, {:#x}",
                    (a >> 3),
                    0xc0 | (if *o == "shl" {
                        4
                    } else if *o == "shr" {
                        5
                    } else {
                        7
                    }) << 3
                        | (a & 7)
                ),
            )
        }
        45 => {
            let o = g.rng.pick(&["shl", "shr", "sar"]);
            let a = g.vreg();
            g.st.r[1] = g.rng.val();
            ("shift r64,cl", format!("{o} {}, cl", R64[a]))
        }
        46 => {
            let o = g.rng.pick(&["shl", "shr", "sar"]);
            let a = g.vreg();
            g.st.r[1] = g.rng.val();
            ("shift r32,cl", format!("{o} {}, cl", R32[a]))
        }
        47 => {
            let o = g.rng.pick(&["shl", "shr", "sar"]);
            let m = g.mem("qword");
            let n = g.rng.below(64);
            ("shift m64,imm", format!("{o} {m}, {n}"))
        }
        48 => {
            let (a, b) = (g.vreg(), g.vreg());
            ("imul r64,r64", format!("imul {}, {}", R64[a], R64[b]))
        }
        49 => {
            let (a, b) = (g.vreg(), g.vreg());
            ("imul r32,r32", format!("imul {}, {}", R32[a], R32[b]))
        }
        50 => {
            let (a, b) = (g.vreg(), g.vreg());
            let i = g.imm32();
            (
                "imul r64,r64,imm",
                format!("imul {}, {}, {i}", R64[a], R64[b]),
            )
        }
        51 => {
            let (a, b) = (g.vreg(), g.vreg());
            let i = g.imm8();
            (
                "imul r32,r32,imm8",
                format!("imul {}, {}, {i}", R32[a], R32[b]),
            )
        }
        52 => {
            let m = g.mem("qword");
            let a = g.vreg();
            ("imul r64,m64", format!("imul {}, {m}", R64[a]))
        }
        53 | 54 => {
            let w64 = form == 53;
            let o = *g.rng.pick(&["mul", "imul", "div", "idiv"]);
            let s = loop {
                let s = g.vreg();
                if s != 0 && s != 2 {
                    break s;
                }
            };
            let rn = if w64 { R64[s] } else { R32[s] };
            if o == "div" || o == "idiv" {
                // keep the quotient in range (and occasionally test #DE-free edge values)
                let d = loop {
                    let d = g.rng.val();
                    if (if w64 { d } else { d & 0xffff_ffff }) != 0 {
                        break d;
                    }
                };
                g.st.r[s] = d;
                if o == "div" {
                    let dd = if w64 { d } else { d & 0xffff_ffff };
                    g.st.r[2] = g.rng.next_u64() % dd;
                } else {
                    let a = g.st.r[0];
                    g.st.r[2] = if w64 {
                        ((a as i64) >> 63) as u64
                    } else {
                        (((a as i32) >> 31) as u32) as u64 | (g.rng.next_u64() & !0xffff_ffff)
                    };
                    if w64 && d == u64::MAX && a == 1 << 63 {
                        g.st.r[0] = 5;
                    }
                    if !w64 && d as u32 == u32::MAX && a as u32 == 1 << 31 {
                        g.st.r[0] = 5;
                    }
                }
            }
            (
                if w64 { "mul/div r64" } else { "mul/div r32" },
                format!("{o} {rn}"),
            )
        }
        55 => {
            let a = g.vreg();
            ("push r64", format!("push {}", R64[a]))
        }
        56 => {
            let a = g.vreg();
            ("pop r64", format!("pop {}", R64[a]))
        }
        57 => {
            let v = if g.rng.below(2) == 0 {
                g.imm8()
            } else {
                g.imm32()
            };
            ("push imm", format!("push {v}"))
        }
        58 => {
            let m = g.mem("qword");
            ("push m64", format!("push {m}"))
        }
        59 => ("push rsp", "push rsp".into()),
        60 => ("pop rsp", "pop rsp".into()),
        61 => ("call rel32", rel32("0xe8")),
        62 => {
            let a = g.vreg();
            g.st.r[a] = taken;
            g.fixed.push(a);
            ("call r64", format!("call {}", R64[a]))
        }
        63 => {
            g.patch.push((RSP_OFF, taken));
            ("ret", "ret".into())
        }
        64 => ("jmp rel8", rel8(0xeb)),
        65 => ("jmp rel32", rel32("0xe9")),
        66 => {
            let a = g.vreg();
            g.st.r[a] = taken;
            ("jmp r64", format!("jmp {}", R64[a]))
        }
        67 => {
            let c = g.rng.below(16) as u8;
            ("jcc rel8", rel8(0x70 + c))
        }
        68 => {
            let c = g.rng.below(16);
            ("jcc rel32", rel32(&format!("0x0f, {:#x}", 0x80 + c)))
        }
        69 => {
            let c = g.rng.pick(&CC);
            let (a, b) = (g.vreg(), g.vreg());
            ("cmovcc r64,r64", format!("cmov{c} {}, {}", R64[a], R64[b]))
        }
        70 => {
            let c = g.rng.pick(&CC);
            let (a, b) = (g.vreg(), g.vreg());
            ("cmovcc r32,r32", format!("cmov{c} {}, {}", R32[a], R32[b]))
        }
        71 => {
            let c = g.rng.pick(&CC);
            let m = g.mem("qword");
            let a = g.vreg();
            ("cmovcc r64,m64", format!("cmov{c} {}, {m}", R64[a]))
        }
        72 => {
            let c = g.rng.pick(&CC);
            let a = g.vreg();
            let r = if g.rng.below(2) == 0 {
                R8[a]
            } else {
                R8L[a & 7]
            };
            ("setcc r8", format!("set{c} {r}"))
        }
        73 => {
            let c = g.rng.pick(&CC);
            let m = g.mem("byte");
            ("setcc m8", format!("set{c} {m}"))
        }
        74 => {
            let o = g.rng.pick(&["cdqe", "cwde", "cqo", "cdq"]);
            ("cdqe/cqo", o.to_string())
        }
        75 => (
            "nop",
            g.rng
                .pick(&["nop", "nop dword ptr [rax]", "nop word ptr [rax+rax*1+0]"])
                .to_string(),
        ),
        76 => {
            let o = g.rng.pick(&ALU);
            let i = g.imm32();
            (
                "alu eax/rax,imm (short)",
                format!(
                    ".byte 0x48, {:#x}, {}",
                    (ALU.iter().position(|x| x == o).unwrap() * 8 + 5),
                    le32(i)
                ),
            )
        }
        77 => {
            let m = g.mem("qword");
            let a = g.vreg();
            ("xchg m64,r64", format!("xchg {m}, {}", R64[a]))
        }
        78 => {
            let (a, b) = (g.vreg(), g.vreg());
            let r = *g.rng.pick(&[&R64, &R32, &R16]);
            ("xchg r,r", format!("xchg {}, {}", r[a], r[b]))
        }
        79 => {
            let a = g.vreg();
            (
                "xchg eax,r (90+r)",
                format!(".byte {:#x}, {:#x}", 0x48 | (a >> 3), 0x90 + (a & 7)),
            )
        }
        80 => {
            let o = g.rng.pick(&ALU);
            let (a, b) = (g.vreg(), g.vreg());
            ("alu r16,r16", format!("{o} {}, {}", R16[a], R16[b]))
        }
        81 => {
            let o = g.rng.pick(&ALU);
            let a = g.vreg();
            let i = g.rng.val() as u16;
            ("alu r16,imm16", format!("{o} {}, {i}", R16[a]))
        }
        82 => {
            let o = g.rng.pick(&ALU);
            let m = g.mem("word");
            let i = g.imm8();
            ("alu m16,imm8", format!("{o} {m}, {i}"))
        }
        83 => {
            let o = g.rng.pick(&ALU);
            let i = g.rng.val() as u16;
            ("alu ax,imm16", format!("{o} ax, {i}"))
        }
        84 => {
            let a = g.vreg();
            let i = g.rng.val() as u16;
            ("mov r16,imm16", format!("mov {}, {i}", R16[a]))
        }
        85 => {
            let m = g.mem("word");
            let i = g.rng.val() as u16;
            ("mov m16,imm16", format!("mov {m}, {i}"))
        }
        86 => {
            let m = g.mem("word");
            let a = g.vreg();
            (
                "mov m16,r16 / r16,m16",
                if g.rng.below(2) == 0 {
                    format!("mov {m}, {}", R16[a])
                } else {
                    format!("mov {}, {m}", R16[a])
                },
            )
        }
        87 => {
            let (a, b) = (g.vreg(), g.vreg());
            let i = g.rng.val() as i16;
            (
                "imul r16 / test r16",
                if g.rng.below(2) == 0 {
                    format!("imul {}, {}, {i}", R16[a], R16[b])
                } else {
                    format!("test {}, {}", R16[a], R16[b])
                },
            )
        }
        88 => {
            let o = g.rng.pick(&["inc", "dec", "neg", "not"]);
            let a = g.vreg();
            ("unary r16", format!("{o} {}", R16[a]))
        }
        89 => {
            let o = g.rng.pick(&["shl", "shr", "sar", "rol", "ror"]);
            let a = g.vreg();
            let n = g.rng.below(40);
            let r = *g.rng.pick(&[&R8, &R16]);
            ("shift/rot r8/r16,imm", format!("{o} {}, {n}", r[a]))
        }
        90 => {
            let o = g.rng.pick(&["shl", "shr", "sar", "rol", "ror"]);
            let a = g.vreg();
            g.st.r[1] = g.rng.val();
            let r = *g.rng.pick(&[&R8, &R16, &R32, &R64]);
            ("shift/rot r,cl", format!("{o} {}, cl", r[a]))
        }
        91 => {
            let o = g.rng.pick(&["rol", "ror"]);
            let a = g.vreg();
            let n = g.rng.below(70);
            let r = *g.rng.pick(&[&R32, &R64]);
            ("rot r32/64,imm", format!("{o} {}, {n}", r[a]))
        }
        92 => {
            let o = g.rng.pick(&["rol", "ror", "shl", "shr", "sar"]);
            let a = g.vreg();
            let r = *g.rng.pick(&[&R8, &R16, &R32, &R64]);
            ("shift/rot r,1", format!("{o} {}, 1", r[a]))
        }
        93 => {
            let o = g.rng.pick(&["rol", "ror", "shl", "sar"]);
            let sz = *g.rng.pick(&["byte", "word", "dword", "qword"]);
            let m = g.mem(sz);
            let n = g.rng.below(40);
            ("shift/rot m,imm", format!("{o} {m}, {n}"))
        }
        94 => {
            let o = g.rng.pick(&["popcnt", "tzcnt", "lzcnt", "bsf", "bsr"]);
            let (a, b) = (g.vreg(), g.vreg());
            if g.rng.below(4) == 0 {
                g.st.r[b] = 0;
            }
            let r = *g.rng.pick(&[&R16, &R32, &R64]);
            (
                "popcnt/tzcnt/lzcnt/bsf/bsr r,r",
                format!("{o} {}, {}", r[a], r[b]),
            )
        }
        95 => {
            let o = g.rng.pick(&["popcnt", "tzcnt", "lzcnt", "bsf", "bsr"]);
            let m = g.mem("qword");
            let a = g.vreg();
            ("bitcount r64,m64", format!("{o} {}, {m}", R64[a]))
        }
        96 => (
            "prefixed nops",
            g.rng
                .pick(&[
                    ".byte 0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00",
                    ".byte 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00",
                    ".byte 0x66, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00",
                    ".byte 0x66, 0x90",
                    "pause",
                    "endbr64",
                    ".byte 0x0f, 0x1f, 0x40, 0x00",
                    ".byte 0x0f, 0x1f, 0x80, 0, 0, 0, 0",
                ])
                .to_string(),
        ),
        97 => {
            g.patch.push((RSP_OFF, taken));
            ("rep ret", ".byte 0xf3, 0xc3".into())
        }
        98 => {
            let (a, b) = (g.vreg(), g.vreg());
            let w = g.rng.pick(&["movzx", "movsx"]);
            (
                "movzx/movsx r16,r8 / r32,r16",
                if g.rng.below(2) == 0 {
                    format!("{w} {}, {}", R16[a], R8[b])
                } else {
                    format!("{w} {}, {}", R32[a], R16[b])
                },
            )
        }
        99 => {
            let (a, b) = (g.vreg(), g.vreg());
            let c = g.rng.pick(&CC);
            ("cmovcc r16", format!("cmov{c} {}, {}", R16[a], R16[b]))
        }
        100 => {
            let o = g.rng.pick(&["cbw", "cwd"]);
            ("cbw/cwd", o.to_string())
        }
        101 => {
            let o = g.rng.pick(&ALU);
            let a = g.vreg();
            let m = g.mem("word");
            ("alu r16,m16", format!("{o} {}, {m}", R16[a]))
        }
        _ => unreachable!(),
    };
    let _ = &mut g.fixed;
    Case {
        form: name,
        asm,
        st: g.st,
        patch: g.patch,
    }
}
pub const NFORMS: usize = 102;

fn le32(i: i64) -> String {
    let b = (i as i32).to_le_bytes();
    format!("{:#x}, {:#x}, {:#x}, {:#x}", b[0], b[1], b[2], b[3])
}

/// Assemble `.intel_syntax` lines labelled c0..cN; return the bytes of each.
fn assemble(lines: &[String], dir: &Path) -> Result<Vec<Vec<u8>>> {
    let mut src = String::from(".intel_syntax noprefix\n.text\n");
    for (i, l) in lines.iter().enumerate() {
        src += &format!("c{i}: {l}\n");
    }
    src += &format!("c{}: nop\n", lines.len());
    let s = dir.join("t.S");
    let o = dir.join("t.o");
    let b = dir.join("t.bin");
    std::fs::write(&s, src)?;
    let out = Command::new("as")
        .args(["--64", "-o"])
        .arg(&o)
        .arg(&s)
        .output()?;
    if !out.status.success() {
        bail!("as failed: {}", String::from_utf8_lossy(&out.stderr));
    }
    run_ok(
        Command::new("objcopy")
            .args(["-O", "binary", "-j", ".text"])
            .arg(&o)
            .arg(&b),
    )?;
    let bytes = std::fs::read(&b)?;
    let syms = symbols(&o)?;
    (0..lines.len())
        .map(|i| {
            let a = syms[&format!("c{i}")] as usize;
            let e = syms[&format!("c{}", i + 1)] as usize;
            Ok(bytes[a..e].to_vec())
        })
        .collect()
}

fn run_ok(c: &mut Command) -> Result<()> {
    let out = c.output()?;
    if !out.status.success() {
        bail!("{:?} failed: {}", c, String::from_utf8_lossy(&out.stderr));
    }
    Ok(())
}

/// Symbol -> value via nm.
pub fn symbols(obj: &Path) -> Result<BTreeMap<String, u64>> {
    let out = Command::new("nm").arg(obj).output()?;
    let mut m = BTreeMap::new();
    for l in String::from_utf8(out.stdout)?.lines() {
        let f: Vec<&str> = l.split_whitespace().collect();
        if f.len() == 3 {
            m.insert(f[2].to_string(), u64::from_str_radix(f[0], 16)?);
        }
    }
    Ok(m)
}

fn tmpdir(tag: &str) -> Result<PathBuf> {
    let d = std::env::temp_dir().join(format!("wasm-sim-{tag}-{}", std::process::id()));
    std::fs::create_dir_all(&d)?;
    Ok(d)
}

/// Observed result of one run.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Obs {
    status: i32,
    locs: Vec<u64>, // 0..16 regs + rip, then 6 flags
    mem: Vec<u8>,
}

pub fn obs_native(s: &State, mem: &[u8]) -> Obs {
    let mut locs: Vec<u64> = s.r.to_vec();
    locs.push(s.rip);
    for b in [0, 2, 4, 6, 7, 11] {
        locs.push((s.flags >> b) & 1);
    }
    Obs {
        status: 0,
        locs,
        mem: mem.to_vec(),
    }
}

fn load_sim(sim: &Sim, st: &State, rip: u64) -> Vec<(i32, u64)> {
    let _ = sim;
    let mut v: Vec<(i32, u64)> = (0..16).map(|i| (i as i32, st.r[i])).collect();
    v.push((RIP, rip));
    for (k, b) in [0, 2, 4, 6, 7, 11].iter().enumerate() {
        v.push((17 + k as i32, (st.flags >> b) & 1));
    }
    v.push((23, 0));
    v
}

/// Run a simulator from `st` at `rip` until rip ∈ stop (or one step if `stop` is empty).
pub fn obs_sim(
    sim: &mut Sim,
    st: &State,
    rip: u64,
    stop: &[u64],
    fuel: u64,
    data: &mut [u8],
) -> Obs {
    for (l, v) in load_sim(sim, st, rip) {
        sim.set(l, v);
    }
    let mut status = 0;
    if stop.is_empty() {
        status = sim.step();
    } else {
        for _ in 0..fuel {
            status = sim.step();
            if status != 0 || stop.contains(&sim.get(RIP)) {
                break;
            }
        }
    }
    let locs = (0..23).map(|l| sim.get(l)).collect();
    Obs {
        status,
        locs,
        mem: data.to_vec(),
    }
}

pub fn sims_for(
    engine: &wasmtime::Engine,
    module: &wasmtime::Module,
    ranges: Vec<(u64, u64)>,
) -> Result<[Sim; 2]> {
    let mk = |u| -> Result<Sim> {
        let mut h = Host::new(Box::new(RawMem {
            ranges: ranges.clone(),
        }));
        h.undef = u;
        Sim::new(engine, module, h)
    };
    Ok([mk(Undef::Zero)?, mk(Undef::Ones)?])
}

/// Compare; returns a description of mismatches (empty = pass). Locations/bytes where the two
/// simulator runs disagree are undefined and skipped.
pub fn compare(nat: &Obs, s0: &Obs, s1: &Obs) -> String {
    let mut out = String::new();
    if s0.status != 0 || s1.status != 0 {
        return format!("sim status {}/{}", s0.status, s1.status);
    }
    let locnames: Vec<&str> = NAMES[..23].to_vec();
    for (i, name) in locnames.iter().enumerate() {
        if s0.locs[i] != s1.locs[i] {
            continue; // undefined
        }
        if s0.locs[i] != nat.locs[i] {
            out += &format!("{name}: sim {:#x} cpu {:#x}; ", s0.locs[i], nat.locs[i]);
        }
    }
    for i in 0..nat.mem.len() {
        if s0.mem[i] == s1.mem[i] && s0.mem[i] != nat.mem[i] {
            out += &format!("mem+{i:#x}: sim {:#x} cpu {:#x}; ", s0.mem[i], nat.mem[i]);
            break;
        }
    }
    out
}

#[derive(clap::Args)]
pub struct InsnArgs {
    /// simulator: g, m or a path
    #[arg(long, default_value = "g")]
    sim: String,
    /// cases per form
    #[arg(long, default_value_t = 200)]
    per: usize,
    #[arg(long, default_value_t = 1)]
    seed: u64,
    /// only forms whose name contains this
    #[arg(long)]
    only: Option<String>,
    /// show up to this many failures per form
    #[arg(long, default_value_t = 3)]
    show: usize,
}

pub fn insn(a: InsnArgs) -> Result<()> {
    let mut nat = Native::new();
    let data = native::mmap(DATA_LEN, false);
    // SAFETY: fresh mapping of DATA_LEN bytes, used only by this thread.
    let dbuf: &mut [u8] = unsafe { std::slice::from_raw_parts_mut(data, DATA_LEN) };
    let dbase = data as u64;
    let engine = harness::engine();
    let module = harness::load_module(&engine, &super::sim_module_path(&a.sim))?;
    let mut sims = sims_for(
        &engine,
        &module,
        vec![nat.range(), (dbase, dbase + DATA_LEN as u64)],
    )?;
    let mut rng = Rng(a.seed);
    let rel = nat.taken as i64 - nat.fall as i64;
    let dir = tmpdir("insn")?;
    let mut cases = vec![];
    for f in 0..NFORMS {
        for _ in 0..a.per {
            cases.push(gen_case(&mut rng, dbase, rel, nat.taken, f));
        }
    }
    if let Some(o) = &a.only {
        cases.retain(|c| c.form.contains(o.as_str()));
    }
    let bytes = assemble(
        &cases.iter().map(|c| c.asm.clone()).collect::<Vec<_>>(),
        &dir,
    )?;
    // form -> (pass, fail, unsupported)
    let mut tally: BTreeMap<&str, (usize, usize, usize)> = BTreeMap::new();
    let mut shown: BTreeMap<&str, usize> = BTreeMap::new();
    for (c, code) in cases.iter().zip(&bytes) {
        let fill: Vec<u8> = {
            let mut r = Rng(rng.next_u64());
            (0..DATA_LEN).map(|_| r.next_u64() as u8).collect()
        };
        let reset = |d: &mut [u8]| {
            d.copy_from_slice(&fill);
            for (o, v) in &c.patch {
                d[*o as usize..*o as usize + 8].copy_from_slice(&v.to_le_bytes());
            }
        };
        let at = nat.place(code);
        reset(dbuf);
        // SAFETY: generated cases only address the data buffer and end at fall/taken.
        let ns = unsafe { nat.run(&c.st) };
        let no = obs_native(&ns, dbuf);
        reset(dbuf);
        let o0 = obs_sim(&mut sims[0], &c.st, at, &[], 1, dbuf);
        reset(dbuf);
        let o1 = obs_sim(&mut sims[1], &c.st, at, &[], 1, dbuf);
        let t = tally.entry(c.form).or_default();
        if o0.status == 2 {
            t.2 += 1;
            continue;
        }
        let d = compare(&no, &o0, &o1);
        if d.is_empty() {
            t.0 += 1;
        } else {
            t.1 += 1;
            let n = shown.entry(c.form).or_default();
            if *n < a.show {
                *n += 1;
                let hex: String = code.iter().map(|b| format!("{b:02x}")).collect();
                println!(
                    "FAIL [{}] {} ({hex}) flags_in={:#x}: {d}",
                    c.form, c.asm, c.st.flags
                );
                if let Some(f) = &sims[0].fault {
                    println!("   fault: {f}");
                    sims[0].fault = None;
                }
            }
        }
    }
    let (mut p, mut f, mut u) = (0, 0, 0);
    println!("{:<28} {:>6} {:>6} {:>6}", "form", "pass", "fail", "unsup");
    for (k, (a, b, c)) in &tally {
        println!("{k:<28} {a:>6} {b:>6} {c:>6}");
        p += a;
        f += b;
        u += c;
    }
    println!("total: {p} pass, {f} fail, {u} unsupported");
    let _ = std::fs::remove_dir_all(&dir);
    if f > 0 {
        bail!("{f} failures");
    }
    Ok(())
}

// ------------------------------------------------------------------ functions

/// Argument kinds for test functions.
#[derive(Clone, Copy)]
pub enum Arg {
    Any,
    Small(u64),
    NonZero,
    /// pointer to a NUL-terminated string in the data buffer
    Str,
    /// pointer to a buffer in the data buffer (at offset)
    Buf(u64),
    /// pointer to a second string at 0x3c00: a copy of the `Str` one, mutated half of the time
    Str2,
}

/// The functions of tests/funcs.S with their argument kinds.
pub const FUNCS: &[(&str, &[Arg])] = &[
    ("add2", &[Arg::Any, Arg::Any]),
    ("max2", &[Arg::Any, Arg::Any]),
    ("abs1", &[Arg::Any]),
    ("sum_to", &[Arg::Small(3000)]),
    ("strlen1", &[Arg::Str]),
    (
        "memcpy1",
        &[Arg::Buf(0x3000), Arg::Buf(0x3400), Arg::Small(200)],
    ),
    ("gcd", &[Arg::Any, Arg::Any]),
    ("popcount1", &[Arg::Any]),
    ("popcount2", &[Arg::Any]),
    ("fact", &[Arg::Small(24)]),
    ("sw", &[Arg::Small(12)]),
    ("mix", &[Arg::Any, Arg::Any, Arg::Small(64)]),
    ("divs", &[Arg::Any, Arg::NonZero]),
    ("twice_sum", &[Arg::Small(3000), Arg::Any]),
];

/// Assemble a .S file; returns (code bytes, symbol offsets).
pub fn assemble_file(src: &Path) -> Result<(Vec<u8>, BTreeMap<String, u64>)> {
    let dir = tmpdir("fn")?;
    let o = dir.join("f.o");
    let b = dir.join("f.bin");
    run_ok(Command::new("as").args(["--64", "-o"]).arg(&o).arg(src))?;
    run_ok(
        Command::new("objcopy")
            .args(["-O", "binary", "-j", ".text"])
            .arg(&o)
            .arg(&b),
    )?;
    let r = (std::fs::read(&b)?, symbols(&o)?);
    let _ = std::fs::remove_dir_all(&dir);
    Ok(r)
}

pub fn funcs_path() -> PathBuf {
    super::x86_dir().join("tests/funcs.S")
}

/// The C functions of tests/cfuncs.c (gcc -O2) with their argument kinds.
pub const CFUNCS: &[(&str, &[Arg])] = &[
    ("popc", &[Arg::Any]),
    ("sum_arr", &[Arg::Buf(0x3000), Arg::Small(64)]),
    ("strcmp1", &[Arg::Str, Arg::Str2]),
    ("reverse", &[Arg::Buf(0x3000), Arg::Small(300)]),
    ("fib", &[Arg::Small(40)]),
    ("isqrt", &[Arg::Any]),
    ("ctz_clz", &[Arg::Any]),
    ("collatz", &[Arg::Small(100000)]),
    ("is_prime", &[Arg::Small(200000)]),
    ("classify", &[Arg::Small(12)]),
    ("crc32b", &[Arg::Buf(0x3000), Arg::Small(100)]),
    ("sum_bytes", &[Arg::Buf(0x3000), Arg::Small(200)]),
    ("bswap16", &[Arg::Any]),
    ("rotl64", &[Arg::Any, Arg::Any]),
    ("isort", &[Arg::Buf(0x3000), Arg::Small(60)]),
    ("mulhi", &[Arg::Any, Arg::Any]),
    ("sat_add16", &[Arg::Any, Arg::Any]),
];

pub fn cfuncs_path() -> PathBuf {
    super::x86_dir().join("tests/cfuncs.c")
}

/// Compile C with gcc -O2 and link flat at address 0 (text then rodata); returns (bytes, symbols).
pub fn build_c(src: &Path) -> Result<(Vec<u8>, BTreeMap<String, u64>)> {
    let dir = tmpdir("c")?;
    let (o, e, b) = (dir.join("c.o"), dir.join("c.elf"), dir.join("c.bin"));
    run_ok(
        Command::new("gcc")
            .args([
                "-O2",
                "-fcf-protection=none",
                "-fno-stack-protector",
                "-fno-asynchronous-unwind-tables",
                "-c",
                "-o",
            ])
            .arg(&o)
            .arg(src),
    )?;
    run_ok(
        Command::new("ld")
            .args(["-N", "-Ttext=0", "-e", "0", "--no-warn-rwx-segments", "-o"])
            .arg(&e)
            .arg(&o),
    )?;
    run_ok(
        Command::new("objcopy")
            .args(["-O", "binary"])
            .arg(&e)
            .arg(&b),
    )?;
    let r = (std::fs::read(&b)?, symbols(&e)?);
    let _ = std::fs::remove_dir_all(&dir);
    Ok(r)
}

/// A test suite: code, symbols, functions with argument kinds.
pub struct Suite {
    pub code: Vec<u8>,
    pub syms: BTreeMap<String, u64>,
    pub funcs: &'static [(&'static str, &'static [Arg])],
}

pub fn suite(c: bool) -> Result<Suite> {
    let (code, syms) = if c {
        build_c(&cfuncs_path())?
    } else {
        assemble_file(&funcs_path())?
    };
    Ok(Suite {
        code,
        syms,
        funcs: if c { CFUNCS } else { FUNCS },
    })
}

pub fn gen_args(rng: &mut Rng, kinds: &[Arg], dbase: u64, mem: &mut [u8]) -> Vec<u64> {
    kinds
        .iter()
        .map(|k| match k {
            Arg::Any => rng.val(),
            Arg::Small(n) => rng.below(*n),
            Arg::NonZero => loop {
                let v = rng.val();
                if v != 0 && v != u64::MAX {
                    break v;
                }
            },
            Arg::Str => {
                let off = 0x3800;
                let len = rng.below(300) as usize;
                for i in 0..len {
                    mem[off + i] = 1 + (rng.next_u64() % 255) as u8;
                }
                mem[off + len] = 0;
                dbase + off as u64
            }
            Arg::Buf(o) => dbase + o,
            Arg::Str2 => {
                let (src, dst) = (0x3800usize, 0x3c00usize);
                let mut i = 0;
                loop {
                    mem[dst + i] = mem[src + i];
                    if mem[src + i] == 0 || i > 300 {
                        break;
                    }
                    i += 1;
                }
                if rng.below(2) == 0 {
                    let k = rng.below(i as u64 + 1) as usize;
                    mem[dst + k] = rng.next_u64() as u8;
                }
                mem[dst + 301] = 0;
                dbase + dst as u64
            }
        })
        .collect()
}

#[derive(clap::Args)]
pub struct FnArgs {
    #[arg(long, default_value = "g")]
    sim: String,
    #[arg(long, default_value_t = 300)]
    per: usize,
    #[arg(long, default_value_t = 1)]
    seed: u64,
    #[arg(long)]
    only: Option<String>,
    /// use the gcc -O2 C functions of tests/cfuncs.c
    #[arg(long)]
    c: bool,
}

pub fn functions(a: FnArgs) -> Result<()> {
    let Suite { code, syms, funcs } = suite(a.c)?;
    let mut nat = Native::new();
    let fbase = nat.place_code(&code);
    let data = native::mmap(DATA_LEN, false);
    // SAFETY: fresh mapping used only here.
    let dbuf: &mut [u8] = unsafe { std::slice::from_raw_parts_mut(data, DATA_LEN) };
    let dbase = data as u64;
    let engine = harness::engine();
    let module = harness::load_module(&engine, &super::sim_module_path(&a.sim))?;
    let mut sims = sims_for(
        &engine,
        &module,
        vec![nat.range(), (dbase, dbase + DATA_LEN as u64)],
    )?;
    let mut rng = Rng(a.seed);
    let mut fails = 0;
    for (name, kinds) in funcs {
        if a.only.as_ref().is_some_and(|o| !name.contains(o.as_str())) {
            continue;
        }
        let target = fbase
            + syms
                .get(*name)
                .with_context(|| format!("no symbol {name}"))?;
        let mut call = vec![0xe8u8];
        call.extend_from_slice(&((target as i64 - nat.fall as i64) as i32).to_le_bytes());
        let at = nat.place(&call);
        let (mut pass, mut fail) = (0, 0);
        for _ in 0..a.per {
            let mut fill: Vec<u8> = (0..DATA_LEN).map(|_| rng.next_u64() as u8).collect();
            let mut st = State::default();
            for r in st.r.iter_mut() {
                *r = rng.val();
            }
            st.r[4] = dbase + RSP_OFF;
            st.flags = rng.next_u64() & 0x8d5;
            let args = gen_args(&mut rng, kinds, dbase, &mut fill);
            for (r, v) in [7usize, 6, 2, 1, 8, 9].iter().zip(&args) {
                st.r[*r] = *v;
            }
            dbuf.copy_from_slice(&fill);
            // SAFETY: test functions only touch the buffers given as arguments and the stack.
            let ns = unsafe { nat.run(&st) };
            let no = obs_native(&ns, dbuf);
            dbuf.copy_from_slice(&fill);
            let o0 = obs_sim(&mut sims[0], &st, at, &[nat.fall], 10_000_000, dbuf);
            dbuf.copy_from_slice(&fill);
            let o1 = obs_sim(&mut sims[1], &st, at, &[nat.fall], 10_000_000, dbuf);
            let d = compare(&no, &o0, &o1);
            if d.is_empty() {
                pass += 1;
            } else {
                fail += 1;
                if fail <= 3 {
                    println!("FAIL {name}{:x?}: {d}", args);
                }
            }
        }
        println!("{name:<10} {pass:>5} pass {fail:>5} fail");
        fails += fail;
    }
    if fails > 0 {
        bail!("{fails} failures");
    }
    Ok(())
}

// ------------------------------------------------------------------ lockstep

#[derive(clap::Args)]
pub struct LockArgs {
    /// the two simulators to compare (P-mem)
    #[arg(long, default_value = "g")]
    a: String,
    #[arg(long, default_value = "m")]
    b: String,
    #[arg(long, default_value_t = 50)]
    per: usize,
    #[arg(long, default_value_t = 1)]
    seed: u64,
    /// also compare P-calls (translated program over sim `a`) against P-mem
    #[arg(long)]
    pcalls: bool,
    /// use the gcc -O2 C functions of tests/cfuncs.c
    #[arg(long)]
    c: bool,
}

pub const CODE_BASE: u64 = 0x40_0000;
pub const DATA_BASE: u64 = 0x10_0000;

/// A fresh paged memory with the code at CODE_BASE and a data/stack area at DATA_BASE.
pub fn fresh_mem(code: &[u8], data: &[u8]) -> PageMem {
    let mut m = PageMem::default();
    m.write(CODE_BASE, code);
    m.write(DATA_BASE, data);
    m
}

pub fn lockstep(a: LockArgs) -> Result<()> {
    let Suite { code, syms, funcs } = suite(a.c)?;
    let engine = harness::engine();
    let ma = harness::load_module(&engine, &super::sim_module_path(&a.a))?;
    let mb = harness::load_module(&engine, &super::sim_module_path(&a.b))?;
    let mut rng = Rng(a.seed);
    let mut total_steps = 0u64;
    let mut fails = 0;
    for (name, kinds) in funcs {
        let entry = CODE_BASE + syms[*name];
        for _ in 0..a.per {
            let mut fill: Vec<u8> = (0..DATA_LEN).map(|_| rng.next_u64() as u8).collect();
            let args = gen_args(&mut rng, kinds, DATA_BASE, &mut fill);
            let seed = rng.next_u64();
            let mk = |m: &wasmtime::Module| -> Result<Sim> {
                let mut h = Host::new(Box::new(fresh_mem(&code, &fill)));
                h.undef = Undef::Random(seed);
                let mut s = Sim::new(&engine, m, h)?;
                for l in 0..16 {
                    s.set(l, 0);
                }
                super::sysv_entry_at(&mut s, entry, &args, DATA_BASE + RSP_OFF);
                Ok(s)
            };
            let (mut sa, mut sb) = (mk(&ma)?, mk(&mb)?);
            let mut n = 0;
            loop {
                let (x, y) = (sa.step(), sb.step());
                n += 1;
                let (fa, fb) = (sa.state(NLOCS), sb.state(NLOCS));
                if x != y || fa != fb {
                    fails += 1;
                    println!("DIVERGE {name}{args:x?} after {n} steps: status {x}/{y}");
                    for l in 0..NLOCS as usize {
                        if fa[l] != fb[l] {
                            println!("  {}: {:x?} vs {:x?}", NAMES[l], fa[l], fb[l]);
                        }
                    }
                    break;
                }
                if x != 0 {
                    break;
                }
            }
            total_steps += n;
        }
    }
    println!(
        "lockstep {} vs {}: {} functions x {} runs, {total_steps} steps compared, {fails} divergences",
        a.a,
        a.b,
        funcs.len(),
        a.per
    );
    if a.pcalls {
        super::pcalls::lockstep(&engine, &ma, &code, &syms, funcs, a.per, a.seed)?;
    }
    if fails > 0 {
        bail!("divergences");
    }
    Ok(())
}

// ------------------------------------------------------------------ bench

#[derive(clap::Args)]
pub struct BenchArgs {
    /// iterations of sum_to
    #[arg(long, default_value_t = 2_000_000)]
    n: u64,
}

pub fn bench(a: BenchArgs) -> Result<()> {
    super::pcalls::bench(a.n)
}
