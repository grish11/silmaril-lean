//! Per-instruction granularity (`wasm-sim reduce --granularity insn`): the P-calls body of a
//! straight-line x86-64 function calls one **full step method** per instruction, and the step
//! methods are emitted as WAT text equal, instruction for instruction, to
//! `Silmaril.Sim.X86.G.emit i len` (the certified G simulator: `emitCore` + `rip += len`). Every
//! state between two calls is then an x86 state, which is what `Silmaril.Sim.Reduce.PCalls.xproblem_of_piece`
//! (P-calls soundness) needs. Fragment: `mov r64, r64`, `mov r/m64, imm32` (register form),
//! `movabs r64, imm64`, `add/or/and/sub/xor/cmp r/m64, r64` (register forms, opcodes 01 09 21
//! 29 31 39); the function must end in its only `ret`, which the ISA-level lemma handles.

use anyhow::{Result, bail};
use iced_x86::{Decoder, DecoderOptions, Instruction, Mnemonic, OpKind, Register};
use std::fmt::Write as _;

pub const GLOBALS: [&str; 23] = [
    "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13",
    "r14", "r15", "rip", "cf", "pf", "af", "zf", "sf", "of",
];

const R64: [Register; 16] = [
    Register::RAX,
    Register::RCX,
    Register::RDX,
    Register::RBX,
    Register::RSP,
    Register::RBP,
    Register::RSI,
    Register::RDI,
    Register::R8,
    Register::R9,
    Register::R10,
    Register::R11,
    Register::R12,
    Register::R13,
    Register::R14,
    Register::R15,
];

fn r64(r: Register) -> Option<&'static str> {
    R64.iter().position(|x| *x == r).map(|i| GLOBALS[i])
}

type Code = Vec<String>;

fn gget(l: &str) -> Code {
    vec![format!("global.get ${l}")]
}
fn gset(l: &str) -> Code {
    vec![format!("global.set ${l}")]
}
fn c64(v: i64) -> Code {
    vec![format!("i64.const {v}")]
}
fn op(o: &str) -> Code {
    vec![format!("i64.{o}")]
}
fn cat(parts: &[Code]) -> Code {
    parts.concat()
}
fn msb(e: Code) -> Code {
    cat(&[e, c64(63), op("shr_u")])
}
fn not(e: Code) -> Code {
    cat(&[e, c64(-1), op("xor")])
}
fn zero(e: &Code) -> Code {
    cat(&[
        c64(1),
        msb(cat(&[e.clone(), c64(0), e.clone(), op("sub"), op("or")])),
        op("xor"),
    ])
}

/// `aluCode op d s` of `Silmaril.Sim.X86.G`.
fn alu(o: &str, d: &str, s: &str) -> Code {
    let x = gget(d);
    let y = gget(s);
    let wasm = match o {
        "cmp" => "sub",
        o => o,
    };
    let r = cat(&[x.clone(), y.clone(), op(wasm)]);
    let carry = match o {
        "add" => msb(cat(&[
            x.clone(),
            y.clone(),
            op("and"),
            x.clone(),
            y.clone(),
            op("or"),
            not(r.clone()),
            op("and"),
            op("or"),
        ])),
        "sub" | "cmp" => msb(cat(&[
            not(x.clone()),
            y.clone(),
            op("and"),
            not(cat(&[x.clone(), y.clone(), op("xor")])),
            r.clone(),
            op("and"),
            op("or"),
        ])),
        _ => c64(0),
    };
    let over = match o {
        "add" => msb(cat(&[
            x.clone(),
            r.clone(),
            op("xor"),
            y.clone(),
            r.clone(),
            op("xor"),
            op("and"),
        ])),
        "sub" | "cmp" => msb(cat(&[
            x.clone(),
            y.clone(),
            op("xor"),
            x.clone(),
            r.clone(),
            op("xor"),
            op("and"),
        ])),
        _ => c64(0),
    };
    let mut c = cat(&[
        carry,
        gset("cf"),
        over,
        gset("of"),
        zero(&r),
        gset("zf"),
        msb(r.clone()),
        gset("sf"),
    ]);
    if o != "cmp" {
        c.extend(cat(&[r, gset(d)]));
    }
    c
}

/// One step method: (name, body = `emit i len`).
pub struct Step {
    pub name: String,
    pub lean: String,
    pub body: Code,
    pub len: usize,
}

fn lean_reg(r: &str) -> String {
    format!(".{r}")
}

/// The step method of one instruction, or `None` outside the fragment.
pub fn step(ins: &Instruction, bytes: &[u8]) -> Option<Step> {
    let len = ins.len();
    let opc = bytes
        .iter()
        .find(|b| !(0x40..=0x4f).contains(*b))
        .copied()?;
    let (name, lean, core) = match ins.mnemonic() {
        Mnemonic::Mov
            if ins.op0_kind() == OpKind::Register && ins.op1_kind() == OpKind::Register =>
        {
            let (d, s) = (r64(ins.op0_register())?, r64(ins.op1_register())?);
            (
                format!("s_mov_{d}_{s}_{len}"),
                format!("(.mov .q (.reg {}) {}, {len})", lean_reg(d), lean_reg(s)),
                cat(&[gget(s), gset(d)]),
            )
        }
        Mnemonic::Mov
            if ins.op0_kind() == OpKind::Register
                && ins.op1_kind() == OpKind::Immediate32to64
                && opc == 0xc7 =>
        {
            let d = r64(ins.op0_register())?;
            let v = ins.immediate32to64();
            (
                format!("s_movi_{d}_{len}_{}", v as u64),
                format!(
                    "(.movI .q (.reg {}) {}, {len})",
                    lean_reg(d),
                    (v as i32) as i64 as u64 & 0xffff_ffff
                ),
                cat(&[c64(v), gset(d)]),
            )
        }
        Mnemonic::Mov
            if ins.op0_kind() == OpKind::Register && ins.op1_kind() == OpKind::Immediate64 =>
        {
            let d = r64(ins.op0_register())?;
            let v = ins.immediate64() as i64;
            (
                format!("s_movabs_{d}_{len}_{}", v as u64),
                format!("(.movabs {} {}, {len})", lean_reg(d), v as u64),
                cat(&[c64(v), gset(d)]),
            )
        }
        m @ (Mnemonic::Add
        | Mnemonic::Or
        | Mnemonic::And
        | Mnemonic::Sub
        | Mnemonic::Xor
        | Mnemonic::Cmp)
            if ins.op0_kind() == OpKind::Register
                && ins.op1_kind() == OpKind::Register
                && matches!(opc, 0x01 | 0x09 | 0x21 | 0x29 | 0x31 | 0x39) =>
        {
            let o = format!("{m:?}").to_lowercase();
            let (d, s) = (r64(ins.op0_register())?, r64(ins.op1_register())?);
            (
                format!("s_{o}_{d}_{s}_{len}"),
                format!(
                    "(.alu .q .{o} (.reg {}) {}, {len})",
                    lean_reg(d),
                    lean_reg(s)
                ),
                alu(&o, d, s),
            )
        }
        _ => return None,
    };
    let body = cat(&[core, gget("rip"), c64(len as i64), op("add"), gset("rip")]);
    Some(Step {
        name,
        lean,
        body,
        len,
    })
}

/// A straight-line leaf function in the fragment: its steps (in order) and the `ret`.
pub struct Leaf {
    pub steps: Vec<Step>,
    /// Bytes of each instruction, `ret` last.
    pub bytes: Vec<Vec<u8>>,
}

pub fn leaf(name: &str, code: &[u8], addr: u64) -> Result<Leaf> {
    let mut d = Decoder::with_ip(64, code, addr, DecoderOptions::NONE);
    let mut steps = vec![];
    let mut bytes = vec![];
    while d.can_decode() {
        let pos = d.position();
        let ins = d.decode();
        let b = code[pos..pos + ins.len()].to_vec();
        if ins.mnemonic() == Mnemonic::Ret && ins.op_count() == 0 {
            bytes.push(b);
            if d.can_decode() {
                bail!("{name}: code after ret");
            }
            return Ok(Leaf { steps, bytes });
        }
        match step(&ins, &b) {
            Some(s) => steps.push(s),
            None => bail!(
                "{name}: {ins} at {:#x} is outside the certified G fragment (insn granularity)",
                ins.ip()
            ),
        }
        bytes.push(b);
    }
    bail!("{name}: no final ret")
}

/// The merged module: the 23 location globals (exported), one step method per distinct
/// instruction (exported), and the P-calls body `<name>_body` calling them in order.
pub fn merged_module(name: &str, l: &Leaf) -> (String, Vec<usize>) {
    let mut w = String::new();
    let mut order: Vec<&Step> = vec![];
    for s in &l.steps {
        if !order.iter().any(|o| o.name == s.name) {
            order.push(s);
        }
    }
    let idx: Vec<usize> = l
        .steps
        .iter()
        .map(|s| order.iter().position(|o| o.name == s.name).unwrap())
        .collect();
    let _ = writeln!(
        w,
        ";; Per-instruction P-calls problem for `{name}` (GENERATED by `wasm-sim reduce --granularity insn`)."
    );
    let _ = writeln!(
        w,
        ";; Step methods = `Silmaril.Sim.X86.G.emit i len` (certified); `{name}_body` calls one per"
    );
    let _ = writeln!(
        w,
        ";; instruction (the final `ret` is handled at the ISA level)."
    );
    let _ = writeln!(w, "(module");
    for g in GLOBALS {
        let _ = writeln!(
            w,
            "  (global ${g} (export \"{g}\") (mut i64) (i64.const 0))"
        );
    }
    for s in &order {
        let _ = writeln!(w, "  (func ${} (export \"{}\")", s.name, s.name);
        for i in &s.body {
            let _ = writeln!(w, "    {i}");
        }
        let _ = writeln!(w, "  )");
    }
    let _ = writeln!(w, "  (func ${name}_body (export \"{name}_body\")");
    for s in &l.steps {
        let _ = writeln!(w, "    call ${}", s.name);
    }
    let _ = writeln!(w, "  )");
    let _ = writeln!(w, ")");
    (w, idx)
}
