//! Rust mirror of the WAT decoder (`parts/core.wat` + `grp-*.wat`), itself a
//! mirror of Silmaril.RiscV.Ext.decode (+ ECALL). Used by the program-as-calls
//! translator and by the random tests. Accepts exactly the canonical encodings.

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Kind {
    /// `(rd, rs1, rs2)`
    R,
    /// `(rd, rs1, imm i64)` (shift amounts too)
    I,
    /// `(rd, imm i64)`
    U,
    /// load `(rd, rs1, off) -> i32`
    L,
    /// store `(rs1, rs2, off) -> i32`
    S,
    /// branch `(rs1, rs2, off) -> i32`: 0 fallthrough, 1 taken, 3 fault
    B,
    /// `(rd, off) -> i32`
    J,
    /// `(rd, rs1, off) -> i32`
    Jr,
    /// `() -> i32`
    Z,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Inst {
    pub m: &'static str,
    pub group: &'static str,
    pub kind: Kind,
    pub rd: u32,
    pub rs1: u32,
    pub rs2: u32,
    pub imm: i64,
}

fn imm_i(w: u32) -> i64 {
    (w as i32 >> 20) as i64
}
fn imm_s(w: u32) -> i64 {
    (((w as i32 >> 25) << 5) | ((w >> 7) & 31) as i32) as i64
}
fn imm_b(w: u32) -> i64 {
    (((w as i32 >> 31) << 12)
        | (((w >> 7) & 1) << 11) as i32
        | (((w >> 25) & 63) << 5) as i32
        | (((w >> 8) & 15) << 1) as i32) as i64
}
fn imm_j(w: u32) -> i64 {
    (((w as i32 >> 31) << 20)
        | (w & 0xFF000) as i32
        | (((w >> 20) & 1) << 11) as i32
        | (((w >> 21) & 0x3FF) << 1) as i32) as i64
}

pub fn decode(w: u32) -> Option<Inst> {
    use Kind::*;
    let rd = (w >> 7) & 31;
    let rs1 = (w >> 15) & 31;
    let rs2 = (w >> 20) & 31;
    let f3 = (w >> 12) & 7;
    let f7 = w >> 25;
    let f6 = w >> 26;
    let mk = |m, group, kind, imm| {
        Some(Inst {
            m,
            group,
            kind,
            rd,
            rs1,
            rs2,
            imm,
        })
    };
    if w & 3 != 3 {
        return None;
    }
    match w & 0x7f {
        0x13 => {
            let imm = imm_i(w);
            match f3 {
                0 => mk("addi", "base", I, imm),
                1 if f6 == 0 => mk("slli", "base", I, imm & 63),
                2 => mk("slti", "base", I, imm),
                3 => mk("sltiu", "base", I, imm),
                4 => mk("xori", "base", I, imm),
                5 if f6 == 0 => mk("srli", "base", I, imm & 63),
                5 if f6 == 0x10 => mk("srai", "base", I, imm & 63),
                6 => mk("ori", "base", I, imm),
                7 => mk("andi", "base", I, imm),
                _ => None,
            }
        }
        0x33 if f7 == 1 => {
            const M: [&str; 8] = [
                "mul", "mulh", "mulhsu", "mulhu", "div", "divu", "rem", "remu",
            ];
            mk(M[f3 as usize], "mul", R, 0)
        }
        0x33 => match (f7, f3) {
            (0, 0) => mk("add", "base", R, 0),
            (0x20, 0) => mk("sub", "base", R, 0),
            (0, 1) => mk("sll", "base", R, 0),
            (0, 2) => mk("slt", "base", R, 0),
            (0, 3) => mk("sltu", "base", R, 0),
            (0, 4) => mk("xor", "base", R, 0),
            (0, 5) => mk("srl", "base", R, 0),
            (0x20, 5) => mk("sra", "base", R, 0),
            (0, 6) => mk("or", "base", R, 0),
            (0, 7) => mk("and", "base", R, 0),
            _ => None,
        },
        0x37 => mk("lui", "base", U, (w & 0xFFFFF000) as i32 as i64),
        0x17 => mk("auipc", "base", U, (w & 0xFFFFF000) as i32 as i64),
        0x1B => match (f3, f7) {
            (0, _) => mk("addiw", "word", I, imm_i(w)),
            (1, 0) => mk("slliw", "word", I, rs2 as i64),
            (5, 0) => mk("srliw", "word", I, rs2 as i64),
            (5, 0x20) => mk("sraiw", "word", I, rs2 as i64),
            _ => None,
        },
        0x3B if f7 == 1 => match f3 {
            0 => mk("mulw", "mul", R, 0),
            4 => mk("divw", "mul", R, 0),
            5 => mk("divuw", "mul", R, 0),
            6 => mk("remw", "mul", R, 0),
            7 => mk("remuw", "mul", R, 0),
            _ => None,
        },
        0x3B => match (f7, f3) {
            (0, 0) => mk("addw", "word", R, 0),
            (0x20, 0) => mk("subw", "word", R, 0),
            (0, 1) => mk("sllw", "word", R, 0),
            (0, 5) => mk("srlw", "word", R, 0),
            (0x20, 5) => mk("sraw", "word", R, 0),
            _ => None,
        },
        0x03 => {
            const L_: [&str; 7] = ["lb", "lh", "lw", "ld", "lbu", "lhu", "lwu"];
            if f3 == 7 {
                None
            } else {
                mk(L_[f3 as usize], "mem", L, imm_i(w))
            }
        }
        0x23 => {
            const S_: [&str; 4] = ["sb", "sh", "sw", "sd"];
            if f3 > 3 {
                None
            } else {
                mk(S_[f3 as usize], "mem", S, imm_s(w))
            }
        }
        0x63 => {
            let m = match f3 {
                0 => "beq",
                1 => "bne",
                4 => "blt",
                5 => "bge",
                6 => "bltu",
                7 => "bgeu",
                _ => return None,
            };
            mk(m, "ctrl", B, imm_b(w))
        }
        0x6F => mk("jal", "ctrl", J, imm_j(w)),
        0x67 if f3 == 0 => mk("jalr", "ctrl", Jr, imm_i(w)),
        0x73 if w == 0x0010_0073 => mk("ebreak", "ctrl", Z, 0),
        0x73 if w == 0x0000_0073 => mk("ecall", "sys", Z, 0),
        _ => None,
    }
}

/// Canonical encoder for the subset used by random tests (inverse of decode).
pub fn encode(i: &Inst) -> u32 {
    let (rd, rs1, rs2) = (i.rd, i.rs1, i.rs2);
    let r = |f7: u32, f3: u32, op: u32| {
        (f7 << 25) | (rs2 << 20) | (rs1 << 15) | (f3 << 12) | (rd << 7) | op
    };
    let ii = |imm: i64, f3: u32, op: u32| {
        (((imm as u32) & 0xFFF) << 20) | (rs1 << 15) | (f3 << 12) | (rd << 7) | op
    };
    let sh = |f6: u32, f3: u32, op: u32| {
        (f6 << 26) | (((i.imm as u32) & 63) << 20) | (rs1 << 15) | (f3 << 12) | (rd << 7) | op
    };
    match i.m {
        "addi" => ii(i.imm, 0, 0x13),
        "slti" => ii(i.imm, 2, 0x13),
        "sltiu" => ii(i.imm, 3, 0x13),
        "xori" => ii(i.imm, 4, 0x13),
        "ori" => ii(i.imm, 6, 0x13),
        "andi" => ii(i.imm, 7, 0x13),
        "slli" => sh(0, 1, 0x13),
        "srli" => sh(0, 5, 0x13),
        "srai" => sh(0x10, 5, 0x13),
        "addiw" => ii(i.imm, 0, 0x1B),
        "slliw" => sh(0, 1, 0x1B),
        "srliw" => sh(0, 5, 0x1B),
        "sraiw" => sh(0x10, 5, 0x1B),
        "lui" | "auipc" => {
            ((i.imm as u32) & 0xFFFFF000) | (rd << 7) | if i.m == "lui" { 0x37 } else { 0x17 }
        }
        m => {
            let base = ["add", "sll", "slt", "sltu", "xor", "srl", "or", "and"];
            let mul = [
                "mul", "mulh", "mulhsu", "mulhu", "div", "divu", "rem", "remu",
            ];
            let mulw = ["mulw", "", "", "", "divw", "divuw", "remw", "remuw"];
            if let Some(k) = base.iter().position(|&x| x == m) {
                r(0, k as u32, 0x33)
            } else if let Some(k) = mul.iter().position(|&x| x == m) {
                r(1, k as u32, 0x33)
            } else if let Some(k) = mulw.iter().position(|&x| x == m) {
                r(1, k as u32, 0x3B)
            } else {
                match m {
                    "sub" => r(0x20, 0, 0x33),
                    "sra" => r(0x20, 5, 0x33),
                    "addw" => r(0, 0, 0x3B),
                    "subw" => r(0x20, 0, 0x3B),
                    "sllw" => r(0, 1, 0x3B),
                    "srlw" => r(0, 5, 0x3B),
                    "sraw" => r(0x20, 5, 0x3B),
                    _ => panic!("encode: unsupported {m}"),
                }
            }
        }
    }
}
