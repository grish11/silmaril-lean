//! Reduction of RV64 problems to Wasm problems ("P-locals"), with decomposition.
//!
//! Input: a reduction plan `*.toml` in the reduction-plan format
//! (`schema = "silmaril.wasm-sim.reduce.v0"`, see `examples/wasm-sim/reduce/toy/reduce.toml`): `[defs]` SMT definitions, `[[function]]` contracts with
//! `requires`/`ensures` over `(reg r)` (value at return) and `(old (reg r))`
//! (value at entry), memory terms `(mem8|mem16|mem32|mem64 addr)`, footprints
//! `reads`/`writes = [[addr, len], ...]`, loop cuts `[[function.cut]] at = <byte
//! offset of the loop header>`, and runtime tests `[[function.test]] args = [...]`.
//!
//! Output, one Wasm problem per function (the decomposition), `modules/<f>.wat`:
//! * registers are i64 locals named by their ABI names; params = live-in
//!   registers (+ the registers whose entry value is checked); result = a0 for
//!   the root, or a0 followed by the caller-saved registers the function may
//!   change when it is a callee of another function in the plan;
//! * each instruction is the body of its simulator method `i_<m>`
//!   (`parts/grp-*.wat`) with `$rget k`/`$rset k` replaced by `local.get/set`
//!   of register k, `$pc_get` by the constant pc, and the `mem.*` imports by
//!   accesses to the imported memory `env.memory` (RV address = Wasm address;
//!   misaligned or out-of-memory accesses trap = fault, as in the simulators);
//! * a call (`jal ra, g` or `auipc ra; jalr ra, off(ra)`) of a function `g` of
//!   the plan becomes a call of the import `g.g` annotated with g's contract
//!   (`;; @assume`): assume-guarantee, with g's own problem in `modules/g.wat`;
//! * `ret` checks the ABI obligations (ra and every callee-saved register the
//!   function writes are equal to their entry values) and traps otherwise, so
//!   total correctness of the Wasm function includes the calling convention;
//! * structured control flow from the reducible CFG (dominator-tree algorithm
//!   of Ramsey, "Beyond Relooper"); loop headers carry `;; @invariant` /
//!   `;; @decreases` (`TODO` when the plan gives no cut).
//!
//! Plus `pieces/ag/<f>/piece.json`, `dag.json` (`silmaril.wasm-sim.piece.v0`, `silmaril.wasm-sim.dag.v0`) and
//! `reduction.toml` (words, signatures, transfer statement).
//! Not covered: ecall, indirect calls, tail calls, recursion, irreducible CFGs.

use super::decode::{Inst, Kind, decode};
use super::elf::Elf;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;
use std::path::Path;
use wasmtime::error::{Result, bail, format_err};

pub const ABI: [&str; 32] = [
    "zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2", "s0", "s1", "a0", "a1", "a2", "a3", "a4",
    "a5", "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11", "t3", "t4",
    "t5", "t6",
];
const RA: u32 = 1;
const A0: u32 = 10;

fn reg_of(name: &str) -> Option<u32> {
    ABI.iter()
        .position(|&n| n == name)
        .map(|i| i as u32)
        .or_else(|| name.strip_prefix('x')?.parse().ok().filter(|&i| i < 32))
}
fn callee_saved(r: u32) -> bool {
    matches!(r, 2..=4 | 8 | 9 | 18..=27)
}
fn caller_saved(r: u32) -> bool {
    matches!(r, 5..=7 | 10..=17 | 28..=31)
}

pub struct Cut {
    pub at: u64,
    pub invariant: String,
    pub decreases: Option<String>,
}

#[derive(Clone, Debug)]
pub enum Arg {
    Int(u64),
    /// address of a test buffer plus offset
    Buf(u64),
}

pub struct FnSpec {
    pub name: String,
    pub requires: String,
    pub ensures: String,
    pub cuts: Vec<Cut>,
    pub reads: Vec<(String, String)>,
    pub writes: Vec<(String, String)>,
    pub tests: Vec<Vec<Arg>>,
    /// registers that hold pointers into the test buffer in random tests
    pub pointers: Vec<u32>,
    pub sample_max: Option<u64>,
    /// (Wasm spec library entry, Lean pre, Lean post) for `--lean`
    pub lean: Option<(String, String, String)>,
}

pub struct Plan {
    pub id: String,
    pub title: String,
    pub root: String,
    pub defs: Vec<String>,
    pub functions: Vec<FnSpec>,
    pub source: String,
    pub lean_prelude: String,
}

pub const BUF: u64 = 0x10_0000;
pub const BUF_LEN: usize = 0x2_0000;

fn s(t: &toml::Table, k: &str, d: &str) -> String {
    t.get(k).and_then(|v| v.as_str()).unwrap_or(d).to_string()
}

fn pairs(t: &toml::Table, k: &str) -> Result<Vec<(String, String)>> {
    let mut out = vec![];
    for v in t.get(k).and_then(|v| v.as_array()).into_iter().flatten() {
        let a = v
            .as_array()
            .ok_or_else(|| format_err!("{k}: expected [addr, len] pairs"))?;
        out.push((
            a[0].as_str().unwrap_or("").into(),
            a[1].as_str().unwrap_or("").into(),
        ));
    }
    Ok(out)
}

pub fn parse_plan(text: &str) -> Result<Plan> {
    let t: toml::Table = text.parse().map_err(|e| format_err!("plan: {e}"))?;
    let mut defs = vec![];
    if let Some(d) = t.get("defs").and_then(|v| v.as_table()) {
        for (_, v) in d {
            defs.push(v.as_str().unwrap_or("").to_string());
        }
    }
    let mut functions = vec![];
    for f in t
        .get("function")
        .and_then(|v| v.as_array())
        .into_iter()
        .flatten()
    {
        let f = f
            .as_table()
            .ok_or_else(|| format_err!("function must be a table"))?;
        let mut cuts = vec![];
        for c in f
            .get("cut")
            .and_then(|v| v.as_array())
            .into_iter()
            .flatten()
        {
            let c = c.as_table().unwrap();
            cuts.push(Cut {
                at: c
                    .get("at")
                    .and_then(|v| v.as_integer())
                    .ok_or_else(|| format_err!("cut needs `at`"))? as u64,
                invariant: s(c, "invariant", "TODO"),
                decreases: c
                    .get("decreases")
                    .and_then(|v| v.as_str())
                    .map(String::from),
            });
        }
        let mut tests = vec![];
        for tt in f
            .get("test")
            .and_then(|v| v.as_array())
            .into_iter()
            .flatten()
        {
            let mut args = vec![];
            for a in tt
                .get("args")
                .and_then(|v| v.as_array())
                .into_iter()
                .flatten()
            {
                args.push(match a {
                    toml::Value::Integer(i) => Arg::Int(*i as u64),
                    toml::Value::String(x) if x.starts_with("buf") => Arg::Buf(
                        x.strip_prefix("buf")
                            .unwrap()
                            .trim_start_matches('+')
                            .parse()
                            .unwrap_or(0),
                    ),
                    _ => bail!("test args: integers or \"buf[+N]\""),
                });
            }
            tests.push(args);
        }
        let pointers = f
            .get("pointers")
            .and_then(|v| v.as_array())
            .into_iter()
            .flatten()
            .filter_map(|v| reg_of(v.as_str()?))
            .collect();
        functions.push(FnSpec {
            name: s(f, "name", ""),
            requires: s(f, "requires", "true"),
            ensures: s(f, "ensures", "true"),
            cuts,
            reads: pairs(f, "reads")?,
            writes: pairs(f, "writes")?,
            tests,
            pointers,
            sample_max: f
                .get("sample_max")
                .and_then(|v| v.as_integer())
                .map(|x| x as u64),
            lean: f
                .get("lean_spec")
                .and_then(|v| v.as_table())
                .map(|l| (s(l, "entry", ""), s(l, "pre", "True"), s(l, "post", "True"))),
        });
    }
    let art = t
        .get("artifact")
        .and_then(|v| v.as_table())
        .cloned()
        .unwrap_or_default();
    Ok(Plan {
        id: s(&t, "id", "wasm-sim/rv64"),
        title: s(&t, "title", ""),
        root: s(
            &t,
            "root",
            &functions
                .first()
                .map(|f| f.name.clone())
                .unwrap_or_default(),
        ),
        defs,
        functions,
        source: s(&art, "source", ""),
        lean_prelude: t
            .get("lean")
            .and_then(|v| v.as_table())
            .map(|l| s(l, "prelude", ""))
            .unwrap_or_default(),
    })
}

/// Rewrite plan state terms into the annotation language of the emitted WAT
/// (wasm-vc style): in requires/ensures `(old (reg r))` and, in requires,
/// `(reg r)` are the parameter `r` (entry value); in ensures `(reg a0)` is
/// `result` and `(reg r)` for another result register is `(result r)`; in
/// invariants `(reg r)` is the current local `r` and `(old (reg r))` is `(old r)`.
#[derive(Clone, Copy, PartialEq)]
enum Ctx {
    Pre,
    Post,
    Inv,
}
fn rewrite(t: &str, ctx: Ctx) -> String {
    let mut out = String::new();
    let mut rest = t;
    while let Some(i) = rest
        .find("(reg ")
        .map(|i| (i, false))
        .into_iter()
        .chain(rest.find("(old (reg ").map(|i| (i, true)))
        .min_by_key(|x| x.0)
    {
        let (i, old) = i;
        out.push_str(&rest[..i]);
        let start = i + if old { 10 } else { 5 };
        let end = start + rest[start..].find(')').unwrap_or(0);
        let r = rest[start..end].trim();
        let close = end + if old { 2 } else { 1 };
        let rep = match (ctx, old) {
            (Ctx::Inv, true) => format!("(old {r})"),
            (Ctx::Inv, false) | (Ctx::Pre, _) | (Ctx::Post, true) => r.to_string(),
            (Ctx::Post, false) => {
                if r == "a0" {
                    "result".into()
                } else {
                    format!("(result {r})")
                }
            }
        };
        out.push_str(&rep);
        rest = &rest[close.min(rest.len())..];
    }
    out.push_str(rest);
    out
}

pub struct Func {
    pub name: String,
    pub base: u64,
    pub insts: Vec<(u64, u32, Inst)>,
}

pub fn extract(elf: &Elf, name: &str) -> Result<Func> {
    let Some(k) = elf.symbols.iter().position(|(n, _)| n == name) else {
        bail!("no symbol {name}")
    };
    let base = elf.symbols[k].1;
    let t = super::translate::text(elf);
    let text_end = t.base + 4 * t.words.len() as u64;
    let end = if elf.sizes[k] > 0 {
        base + elf.sizes[k]
    } else {
        elf.symbols
            .iter()
            .map(|s| s.1)
            .filter(|&a| a > base && a <= text_end)
            .min()
            .unwrap_or(text_end)
    };
    let mut insts = vec![];
    for pc in (base..end).step_by(4) {
        let w = t.words[((pc - t.base) / 4) as usize];
        match decode(w) {
            Some(i) => insts.push((pc, w, i)),
            None => bail!("{name}: undecodable word {w:#010x} at {pc:#x}"),
        }
    }
    Ok(Func {
        name: name.into(),
        base,
        insts,
    })
}

#[derive(Clone, Copy, Debug)]
enum Term {
    /// fall into the next block
    Fall(usize),
    /// conditional branch at instruction index; taken target (None = misaligned: fault), fallthrough
    Cond(usize, Option<usize>, usize),
    Jump(Option<usize>),
    Ret,
}

struct Cfg {
    starts: Vec<usize>,
    ends: Vec<usize>,
    terms: Vec<Term>,
    /// instruction index of a call -> callee address
    calls: BTreeMap<usize, u64>,
}

fn cfg(f: &Func) -> Result<Cfg> {
    let n = f.insts.len();
    let idx = |pc: u64| -> Result<Option<usize>> {
        if !pc.is_multiple_of(4) {
            return Ok(None);
        }
        if pc < f.base || pc >= f.base + 4 * n as u64 {
            bail!(
                "{}: jump to {pc:#x} outside the function (tail calls are not supported)",
                f.name
            )
        }
        Ok(Some(((pc - f.base) / 4) as usize))
    };
    let mut lead = BTreeSet::from([0usize]);
    let mut calls = BTreeMap::new();
    for (k, &(pc, w, i)) in f.insts.iter().enumerate() {
        match i.kind {
            Kind::R | Kind::I | Kind::U | Kind::L | Kind::S => {}
            Kind::J if i.rd == RA => {
                calls.insert(k, pc.wrapping_add(i.imm as u64));
            }
            Kind::B | Kind::J if i.kind == Kind::B || i.rd == 0 => {
                if let Some(t) = idx(pc.wrapping_add(i.imm as u64))? {
                    lead.insert(t);
                }
                lead.insert(k + 1);
            }
            Kind::Jr if i.rd == 0 && i.rs1 == RA && i.imm == 0 => {
                lead.insert(k + 1);
            }
            Kind::Jr
                if i.rd == RA
                    && i.rs1 == RA
                    && k > 0
                    && f.insts[k - 1].2.m == "auipc"
                    && f.insts[k - 1].2.rd == RA =>
            {
                let (ppc, _, p) = f.insts[k - 1];
                calls.insert(k, ppc.wrapping_add(p.imm as u64).wrapping_add(i.imm as u64));
            }
            _ => bail!(
                "{}: {pc:#x}: {w:#010x} ({}) not supported by the reduction",
                f.name,
                i.m
            ),
        }
    }
    // a call must not be split from its auipc
    for &k in calls.keys() {
        if f.insts[k].2.kind == Kind::Jr && lead.contains(&k) {
            bail!("{}: branch target between auipc and jalr of a call", f.name)
        }
    }
    lead.retain(|&k| k < n);
    let starts: Vec<usize> = lead.into_iter().collect();
    let blk = |k: usize| starts.binary_search(&k).unwrap();
    let mut ends = vec![];
    let mut terms = vec![];
    for b in 0..starts.len() {
        let e = starts.get(b + 1).copied().unwrap_or(n);
        let (pc, _, last) = f.insts[e - 1];
        let tgt = |pc: u64, imm: i64| idx(pc.wrapping_add(imm as u64)).map(|o| o.map(blk));
        let is_call = calls.contains_key(&(e - 1));
        let term = match last.kind {
            Kind::B => {
                if e >= n {
                    bail!("{}: falls off the end", f.name)
                }
                Term::Cond(e - 1, tgt(pc, last.imm)?, blk(e))
            }
            Kind::J if !is_call => Term::Jump(tgt(pc, last.imm)?),
            Kind::Jr if !is_call => Term::Ret,
            _ => {
                if e >= n {
                    bail!("{}: falls off the end", f.name)
                }
                Term::Fall(blk(e))
            }
        };
        ends.push(e);
        terms.push(term);
    }
    Ok(Cfg {
        starts,
        ends,
        terms,
        calls,
    })
}

fn succs(t: Term) -> Vec<usize> {
    match t {
        Term::Fall(b) | Term::Jump(Some(b)) => vec![b],
        Term::Cond(_, Some(a), b) => vec![a, b],
        Term::Cond(_, None, b) => vec![b],
        _ => vec![],
    }
}

fn g(r: u32) -> String {
    if r == 0 {
        "(i64.const 0)".into()
    } else {
        format!("(local.get ${})", ABI[r as usize])
    }
}
fn set(r: u32, e: String) -> String {
    if r == 0 {
        format!("(drop {e})")
    } else {
        format!("(local.set ${} {e})", ABI[r as usize])
    }
}

/// The method body of `i_<m>` specialised to constant registers and pc.
fn snippet(i: &Inst, pc: u64, helpers: &mut BTreeSet<&'static str>) -> String {
    let (a, b, imm) = (g(i.rs1), g(i.rs2), i.imm);
    let c = |x: i64| format!("(i64.const {x})");
    let w = |e: String| format!("(i32.wrap_i64 {e})");
    let sx = |e: String| format!("(i64.extend_i32_s {e})");
    let bin = |op: &str, y: String| format!("({op} {a} {y})");
    let mut call = |h: &'static str, x: String, y: String| {
        helpers.insert(h);
        format!("(call ${h} {x} {y})")
    };
    let e = match i.m {
        "addi" => bin("i64.add", c(imm)),
        "slti" => format!("(i64.extend_i32_u {})", bin("i64.lt_s", c(imm))),
        "sltiu" => format!("(i64.extend_i32_u {})", bin("i64.lt_u", c(imm))),
        "xori" => bin("i64.xor", c(imm)),
        "ori" => bin("i64.or", c(imm)),
        "andi" => bin("i64.and", c(imm)),
        "slli" => bin("i64.shl", c(imm)),
        "srli" => bin("i64.shr_u", c(imm)),
        "srai" => bin("i64.shr_s", c(imm)),
        "add" => bin("i64.add", b.clone()),
        "sub" => bin("i64.sub", b.clone()),
        "sll" => bin("i64.shl", b.clone()),
        "slt" => format!("(i64.extend_i32_u {})", bin("i64.lt_s", b.clone())),
        "sltu" => format!("(i64.extend_i32_u {})", bin("i64.lt_u", b.clone())),
        "xor" => bin("i64.xor", b.clone()),
        "srl" => bin("i64.shr_u", b.clone()),
        "sra" => bin("i64.shr_s", b.clone()),
        "or" => bin("i64.or", b.clone()),
        "and" => bin("i64.and", b.clone()),
        "lui" => c(imm),
        "auipc" => c(pc.wrapping_add(imm as u64) as i64),
        "addiw" => sx(format!("(i32.add {} {})", w(a.clone()), w(c(imm)))),
        "slliw" => sx(format!("(i32.shl {} {})", w(a.clone()), w(c(imm)))),
        "srliw" => sx(format!("(i32.shr_u {} {})", w(a.clone()), w(c(imm)))),
        "sraiw" => sx(format!("(i32.shr_s {} {})", w(a.clone()), w(c(imm)))),
        "addw" => sx(format!("(i32.add {} {})", w(a.clone()), w(b.clone()))),
        "subw" => sx(format!("(i32.sub {} {})", w(a.clone()), w(b.clone()))),
        "sllw" => sx(format!("(i32.shl {} {})", w(a.clone()), w(b.clone()))),
        "srlw" => sx(format!("(i32.shr_u {} {})", w(a.clone()), w(b.clone()))),
        "sraw" => sx(format!("(i32.shr_s {} {})", w(a.clone()), w(b.clone()))),
        "mul" => bin("i64.mul", b.clone()),
        "mulh" => call("mulh64", a.clone(), b.clone()),
        "mulhsu" => call("mulhsu64", a.clone(), b.clone()),
        "mulhu" => call("mulhu64", a.clone(), b.clone()),
        "div" => call("divs64", a.clone(), b.clone()),
        "divu" => call("divu64", a.clone(), b.clone()),
        "rem" => call("rems64", a.clone(), b.clone()),
        "remu" => call("remu64", a.clone(), b.clone()),
        "mulw" => sx(format!("(i32.mul {} {})", w(a.clone()), w(b.clone()))),
        "divw" => sx(call("divs32", w(a.clone()), w(b.clone()))),
        "divuw" => sx(call("divu32", w(a.clone()), w(b.clone()))),
        "remw" => sx(call("rems32", w(a.clone()), w(b.clone()))),
        "remuw" => sx(call("remu32", w(a.clone()), w(b.clone()))),
        m => unreachable!("snippet {m}"),
    };
    set(i.rd, e)
}

fn cond(i: &Inst) -> String {
    let op = match i.m {
        "beq" => "i64.eq",
        "bne" => "i64.ne",
        "blt" => "i64.lt_s",
        "bge" => "i64.ge_s",
        "bltu" => "i64.lt_u",
        _ => "i64.ge_u",
    };
    format!("({op} {} {})", g(i.rs1), g(i.rs2))
}

/// Extract `(func $name ...)` from a WAT part by parenthesis matching.
fn wat_func(src: &str, name: &str) -> String {
    let start = src
        .find(&format!("(func ${name} "))
        .unwrap_or_else(|| panic!("helper {name}"));
    let mut depth = 0;
    for (k, ch) in src[start..].char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return src[start..start + k + 1].to_string();
                }
            }
            _ => {}
        }
    }
    unreachable!()
}

/// Signature of a translated function: params and results (registers).
#[derive(Clone, Debug)]
pub struct Sig {
    pub params: Vec<u32>,
    pub results: Vec<u32>,
}

/// Per-function analysis.
struct Analysis {
    f: Func,
    c: Cfg,
    callees: BTreeMap<usize, String>,
    written: BTreeSet<u32>,
    live_in: BTreeSet<u32>,
    uses_mem: bool,
}

fn analyse(elf: &Elf, name: &str, names: &BTreeMap<u64, String>) -> Result<Analysis> {
    let f = extract(elf, name)?;
    let c = cfg(&f)?;
    let mut callees = BTreeMap::new();
    for (&k, &a) in &c.calls {
        match names.get(&a) {
            Some(g) => {
                callees.insert(k, g.clone());
            }
            None => bail!(
                "{name}: call of {a:#x}, which is not a function of the plan (add it with a contract)"
            ),
        }
    }
    let uses_mem = f
        .insts
        .iter()
        .any(|(_, _, i)| matches!(i.kind, Kind::L | Kind::S));
    Ok(Analysis {
        f,
        c,
        callees,
        written: BTreeSet::new(),
        live_in: BTreeSet::new(),
        uses_mem,
    })
}

/// Registers read / written by instruction k (calls via the callee signature).
fn rw(a: &Analysis, k: usize, sigs: &BTreeMap<String, Sig>) -> (Vec<u32>, Vec<u32>) {
    let i = a.f.insts[k].2;
    if let Some(g) = a.callees.get(&k) {
        let sig = &sigs[g];
        let mut w = sig.results.clone();
        w.push(RA);
        let r = sig
            .params
            .iter()
            .copied()
            .filter(|&p| p != RA)
            .chain((i.kind == Kind::Jr).then_some(RA))
            .collect();
        return (r, w);
    }
    match i.kind {
        Kind::R => (vec![i.rs1, i.rs2], vec![i.rd]),
        Kind::I | Kind::L => (vec![i.rs1], vec![i.rd]),
        Kind::U => (vec![], vec![i.rd]),
        Kind::S | Kind::B => (vec![i.rs1, i.rs2], vec![]),
        Kind::Jr => (vec![RA], vec![]),
        _ => (vec![], vec![]),
    }
}

fn dataflow(a: &mut Analysis, sigs: &BTreeMap<String, Sig>) {
    let nb = a.c.starts.len();
    let mut uses = vec![BTreeSet::new(); nb];
    let mut defs = vec![BTreeSet::new(); nb];
    let mut written = BTreeSet::new();
    for b in 0..nb {
        for k in a.c.starts[b]..a.c.ends[b] {
            let (r, w) = rw(a, k, sigs);
            for x in r {
                if x != 0 && !defs[b].contains(&x) {
                    uses[b].insert(x);
                }
            }
            for x in w.into_iter().filter(|&x| x != 0) {
                defs[b].insert(x);
                written.insert(x);
            }
        }
    }
    let succ: Vec<Vec<usize>> = a.c.terms.iter().map(|&t| succs(t)).collect();
    let mut live = vec![BTreeSet::new(); nb];
    let mut changed = true;
    while changed {
        changed = false;
        for b in (0..nb).rev() {
            let mut out: BTreeSet<u32> = BTreeSet::new();
            for &s in &succ[b] {
                out.extend(live[s].iter().copied());
            }
            let mut li: BTreeSet<u32> = out.difference(&defs[b]).copied().collect();
            li.extend(uses[b].iter().copied());
            if li != live[b] {
                live[b] = li;
                changed = true;
            }
        }
    }
    a.written = written;
    a.live_in = live[0].clone();
    // `ret` reads ra, but if ra is never written it is the entry return address by construction
    if !a.written.contains(&RA) {
        a.live_in.remove(&RA);
    }
}

/// Registers whose entry value `ret` must restore: ra and callee-saved registers written.
fn checked(a: &Analysis) -> Vec<u32> {
    a.written
        .iter()
        .copied()
        .filter(|&r| r == RA || callee_saved(r))
        .collect()
}

fn signature(a: &Analysis, as_callee: bool) -> Sig {
    let mut ps: BTreeSet<u32> = a.live_in.clone();
    ps.extend(checked(a));
    ps.insert(A0);
    // ABI argument registers first, then the rest in register order
    let mut params: Vec<u32> = (10..=17).filter(|r| ps.contains(r)).collect();
    params.extend(ps.iter().copied().filter(|r| !(10..=17).contains(r)));
    let mut results = vec![A0];
    if as_callee {
        results.extend(
            a.written
                .iter()
                .copied()
                .filter(|&r| caller_saved(r) && r != A0),
        );
    }
    Sig { params, results }
}

struct Emit<'a> {
    a: &'a Analysis,
    spec: &'a FnSpec,
    sigs: &'a BTreeMap<String, Sig>,
    sig: &'a Sig,
    rpo: Vec<usize>,
    header: Vec<bool>,
    merge: Vec<bool>,
    kids: Vec<Vec<usize>>,
    out: String,
    depth: usize,
    helpers: BTreeSet<&'static str>,
}

fn mem_snippet(i: &Inst) -> String {
    let addr = format!("(i64.add {} (i64.const {}))", g(i.rs1), i.imm);
    let (op, w) = match i.m {
        "lb" => ("i64.load8_s", 1),
        "lbu" => ("i64.load8_u", 1),
        "lh" => ("i64.load16_s", 2),
        "lhu" => ("i64.load16_u", 2),
        "lw" => ("i64.load32_s", 4),
        "lwu" => ("i64.load32_u", 4),
        "ld" => ("i64.load", 8),
        "sb" => ("i64.store8", 1),
        "sh" => ("i64.store16", 2),
        "sw" => ("i64.store32", 4),
        _ => ("i64.store", 8),
    };
    let ea = format!("(call $ea {addr} (i64.const {w}))");
    if i.kind == Kind::L {
        set(i.rd, format!("({op} {ea})"))
    } else {
        format!("({op} {ea} {})", g(i.rs2))
    }
}

impl Emit<'_> {
    fn line(&mut self, s: &str) {
        let _ = writeln!(self.out, "{}{s}", "  ".repeat(self.depth));
    }
    fn tree(&mut self, x: usize) {
        let mut ys: Vec<usize> = self.kids[x]
            .iter()
            .copied()
            .filter(|&y| self.merge[y])
            .collect();
        ys.sort_by_key(|&y| self.rpo[y]);
        if self.header[x] {
            let (pc, _, _) = self.a.f.insts[self.a.c.starts[x]];
            let off = pc - self.a.f.base;
            self.line(&format!("(loop $L{x}"));
            self.depth += 1;
            let cut = self.spec.cuts.iter().find(|c| c.at == off);
            let inv = cut
                .map(|c| rewrite(&c.invariant, Ctx::Inv))
                .unwrap_or_else(|| "TODO".into());
            self.line(&format!(";; cut at +{off} ({pc:#x})"));
            self.line(&format!(";; @invariant {inv}"));
            if let Some(d) = cut.and_then(|c| c.decreases.clone()) {
                self.line(&format!(";; @decreases {}", rewrite(&d, Ctx::Inv)));
            }
            self.within(x, &ys);
            self.depth -= 1;
            self.line(")");
        } else {
            self.within(x, &ys);
        }
    }
    fn within(&mut self, x: usize, ys: &[usize]) {
        if let Some((&last, rest)) = ys.split_last() {
            self.line(&format!("(block $B{last}"));
            self.depth += 1;
            self.within(x, rest);
            self.depth -= 1;
            self.line(")");
            self.tree(last);
            return;
        }
        let (s, e) = (self.a.c.starts[x], self.a.c.ends[x]);
        for k in s..e {
            let (pc, w, i) = self.a.f.insts[k];
            self.line(&format!(";; {pc:#x}: {w:08x} {}", i.m));
            if let Some(callee) = self.a.callees.get(&k).cloned() {
                let sig = &self.sigs[&callee];
                let args: Vec<String> = sig
                    .params
                    .iter()
                    .map(|&p| {
                        if p == RA {
                            format!("(i64.const {})", pc + 4)
                        } else {
                            g(p)
                        }
                    })
                    .collect();
                self.line(&format!("(call ${callee} {})", args.join(" ")));
                let sets: Vec<String> = sig
                    .results
                    .iter()
                    .rev()
                    .map(|&r| set(r, String::new()).replace(" )", ")"))
                    .collect();
                self.line(&sets.join(" "));
                self.line(&format!(
                    "(local.set $ra (i64.const {})) ;; the callee returned to pc + 4",
                    pc + 4
                ));
                continue;
            }
            match i.kind {
                Kind::R | Kind::I | Kind::U => {
                    let sn = snippet(&i, pc, &mut self.helpers);
                    self.line(&sn);
                }
                Kind::L | Kind::S => self.line(&mem_snippet(&i)),
                _ => {}
            }
        }
        match self.a.c.terms[x] {
            Term::Fall(y) | Term::Jump(Some(y)) => self.branch(x, Some(y)),
            Term::Jump(None) => self.line("(unreachable) ;; misaligned jump target: fault"),
            Term::Ret => {
                let chk = checked(self.a);
                if !chk.is_empty() {
                    let eqs: Vec<String> = chk
                        .iter()
                        .map(|&r| {
                            format!(
                                "(i64.eq (local.get ${0}) (local.get ${0}_0))",
                                ABI[r as usize]
                            )
                        })
                        .collect();
                    let all = eqs
                        .into_iter()
                        .reduce(|a, b| format!("(i32.and {a} {b})"))
                        .unwrap();
                    self.line(";; ABI: return to the entry ra, callee-saved registers restored");
                    self.line(&format!("(if (i32.eqz {all}) (then (unreachable)))"));
                }
                let rs: Vec<String> = self.sig.results.iter().map(|&r| g(r)).collect();
                self.line(&format!("(return {})", rs.join(" ")));
            }
            Term::Cond(k, t, f) => {
                let c = cond(&self.a.f.insts[k].2);
                self.line(&format!("(if {c}"));
                self.depth += 1;
                self.line("(then");
                self.depth += 1;
                self.branch(x, t);
                self.depth -= 1;
                self.line(")");
                self.line("(else");
                self.depth += 1;
                self.branch(x, Some(f));
                self.depth -= 1;
                self.line("))");
                self.depth -= 1;
            }
        }
    }
    fn branch(&mut self, src: usize, tgt: Option<usize>) {
        let Some(t) = tgt else {
            self.line("(unreachable) ;; misaligned branch target: fault");
            return;
        };
        if self.rpo[t] <= self.rpo[src] {
            self.line(&format!("(br $L{t})"));
        } else if self.merge[t] {
            self.line(&format!("(br $B{t})"));
        } else {
            self.tree(t);
        }
    }
}

/// Block structure: (reverse post-order, loop headers, merge blocks, dominator-tree children).
type Structure = (Vec<usize>, Vec<bool>, Vec<bool>, Vec<Vec<usize>>);

fn structure(a: &Analysis) -> Result<Structure> {
    let nb = a.c.starts.len();
    let succ: Vec<Vec<usize>> = a.c.terms.iter().map(|&t| succs(t)).collect();
    let mut post = vec![];
    let mut seen = vec![false; nb];
    let mut stack = vec![(0usize, 0usize)];
    seen[0] = true;
    while let Some(&mut (x, ref mut i)) = stack.last_mut() {
        if *i < succ[x].len() {
            let y = succ[x][*i];
            *i += 1;
            if !seen[y] {
                seen[y] = true;
                stack.push((y, 0));
            }
        } else {
            post.push(x);
            stack.pop();
        }
    }
    let order: Vec<usize> = post.iter().rev().copied().collect();
    let mut rpo = vec![usize::MAX; nb];
    for (k, &x) in order.iter().enumerate() {
        rpo[x] = k;
    }
    let mut preds = vec![vec![]; nb];
    for x in order.iter().copied() {
        for &y in &succ[x] {
            preds[y].push(x);
        }
    }
    let mut idom = vec![usize::MAX; nb];
    idom[0] = 0;
    let mut changed = true;
    while changed {
        changed = false;
        for &x in order.iter().skip(1) {
            let mut new = usize::MAX;
            for &p in &preds[x] {
                if idom[p] == usize::MAX {
                    continue;
                }
                new = if new == usize::MAX {
                    p
                } else {
                    let (mut u, mut v) = (p, new);
                    while u != v {
                        while rpo[u] > rpo[v] {
                            u = idom[u];
                        }
                        while rpo[v] > rpo[u] {
                            v = idom[v];
                        }
                    }
                    u
                };
            }
            if idom[x] != new {
                idom[x] = new;
                changed = true;
            }
        }
    }
    let dominates = |d: usize, mut b: usize| loop {
        if d == b {
            return true;
        }
        if b == 0 {
            return false;
        }
        b = idom[b];
    };
    let mut header = vec![false; nb];
    let mut merge = vec![false; nb];
    for &x in &order {
        let mut fwd = 0;
        for &p in &preds[x] {
            if rpo[p] >= rpo[x] {
                if !dominates(x, p) {
                    bail!("{}: irreducible control flow", a.f.name);
                }
                header[x] = true;
            } else {
                fwd += 1;
            }
        }
        merge[x] = fwd >= 2;
    }
    let mut kids = vec![vec![]; nb];
    for &x in order.iter().skip(1) {
        kids[idom[x]].push(x);
    }
    Ok((rpo, header, merge, kids))
}

const MEM_HELPER: &str = r#"  ;; effective address check of the `mem` group methods: misaligned -> fault (Ext.Instr.exec),
  ;; outside the memory -> fault (the environment's `mem.*` import traps)
  (func $ea (param $a i64) (param $w i64) (result i32)
    (if (i32.wrap_i64 (i64.and (local.get $a) (i64.sub (local.get $w) (i64.const 1)))) (then (unreachable)))
    (if (i64.gt_u (local.get $a) (i64.sub (i64.shl (i64.extend_i32_u (memory.size)) (i64.const 16)) (local.get $w)))
      (then (unreachable)))
    (i32.wrap_i64 (local.get $a)))
"#;

fn ty(n: usize, kw: &str) -> String {
    if n == 0 {
        String::new()
    } else {
        format!(" ({kw}{})", " i64".repeat(n))
    }
}

fn emit_module(
    a: &Analysis,
    spec: &FnSpec,
    plan: &Plan,
    sigs: &BTreeMap<String, Sig>,
    specs: &BTreeMap<String, &FnSpec>,
    elf_name: &str,
) -> Result<String> {
    let sig = &sigs[&a.f.name];
    let (rpo, header, merge, kids) = structure(a)?;
    let mut em = Emit {
        a,
        spec,
        sigs,
        sig,
        rpo,
        header,
        merge,
        kids,
        out: String::new(),
        depth: 2,
        helpers: BTreeSet::new(),
    };
    let chk = checked(a);
    for &r in &chk {
        em.line(&format!(
            "(local.set ${0}_0 (local.get ${0}))",
            ABI[r as usize]
        ));
    }
    em.tree(0);
    let body = std::mem::take(&mut em.out);
    let helpers = em.helpers.clone();
    let name = &a.f.name;
    let mut o = String::new();
    writeln!(
        o,
        ";; Wasm problem: RV64 function `{name}` @ {:#x} ({} instructions) of {elf_name}, plan {}",
        a.f.base,
        a.f.insts.len(),
        plan.id
    )?;
    writeln!(
        o,
        ";; Generated by tools/wasm-sim (rv64 reduce, P-locals). Registers are i64 locals (ABI names);"
    )?;
    writeln!(
        o,
        ";; each instruction is its simulator method body (examples/wasm-sim/rv64/parts) specialised"
    )?;
    writeln!(
        o,
        ";; to constant registers and pc; memory is `env.memory`, at least 1024 pages (RV address = Wasm address)."
    )?;
    writeln!(
        o,
        ";; Params are entry values in @requires/@ensures; `result` is a0, `(result r)` another result."
    )?;
    for d in &plan.defs {
        writeln!(o, ";; @define {d}")?;
    }
    writeln!(o, "(module")?;
    if a.uses_mem || a.callees.values().any(|g| specs.contains_key(g)) {
        writeln!(o, "  (import \"env\" \"memory\" (memory 1024))")?;
    }
    let called: BTreeSet<&String> = a.callees.values().collect();
    for g in called {
        let gs = &sigs[g];
        let sp = specs[g];
        writeln!(
            o,
            "  ;; @assume {g} requires {}",
            rewrite(&sp.requires, Ctx::Pre)
        )?;
        writeln!(
            o,
            "  ;; @assume {g} ensures {}",
            rewrite(&sp.ensures, Ctx::Post)
        )?;
        writeln!(
            o,
            "  ;; {g}: params {:?} -> results {:?}",
            gs.params
                .iter()
                .map(|&r| ABI[r as usize])
                .collect::<Vec<_>>(),
            gs.results
                .iter()
                .map(|&r| ABI[r as usize])
                .collect::<Vec<_>>()
        )?;
        writeln!(
            o,
            "  (import \"{g}\" \"{g}\" (func ${g}{}{}))",
            ty(gs.params.len(), "param"),
            ty(gs.results.len(), "result")
        )?;
    }
    writeln!(o, "  ;; @requires {}", rewrite(&spec.requires, Ctx::Pre))?;
    writeln!(o, "  ;; @ensures {}", rewrite(&spec.ensures, Ctx::Post))?;
    for (x, l) in &spec.reads {
        writeln!(
            o,
            "  ;; @reads {} {}",
            rewrite(x, Ctx::Pre),
            rewrite(l, Ctx::Pre)
        )?;
    }
    for (x, l) in &spec.writes {
        writeln!(
            o,
            "  ;; @writes {} {}",
            rewrite(x, Ctx::Pre),
            rewrite(l, Ctx::Pre)
        )?;
    }
    write!(o, "  (func ${name} (export \"{name}\")")?;
    for &p in &sig.params {
        write!(o, " (param ${} i64)", ABI[p as usize])?;
    }
    write!(o, "{}", ty(sig.results.len(), "result"))?;
    for &l in a.written.iter().filter(|r| !sig.params.contains(r)) {
        write!(o, " (local ${} i64)", ABI[l as usize])?;
    }
    for &r in &chk {
        write!(o, " (local ${}_0 i64)", ABI[r as usize])?;
    }
    writeln!(o)?;
    o.push_str(&body);
    writeln!(o, "    (unreachable))")?;
    if a.uses_mem {
        o.push_str(MEM_HELPER);
    }
    if !helpers.is_empty() {
        let src = std::fs::read_to_string(super::asm::parts_dir().join("grp-mul.wat"))?;
        let mut need: BTreeSet<&str> = helpers.iter().copied().collect();
        if need.contains("mulh64") || need.contains("mulhsu64") {
            need.insert("mulhu64");
        }
        writeln!(
            o,
            "  ;; M-extension helpers, verbatim from parts/grp-mul.wat"
        )?;
        for h in need {
            for l in wat_func(&src, h).lines() {
                writeln!(o, "  {l}")?;
            }
        }
    }
    writeln!(o, ")")?;
    Ok(o)
}

fn js(s: &str) -> String {
    format!("{s:?}")
}

pub struct Output {
    pub modules: BTreeMap<String, String>,
    pub sigs: BTreeMap<String, Sig>,
    pub order: Vec<String>,
    pub entries: BTreeMap<String, u64>,
    pub callees: BTreeMap<String, Vec<String>>,
}

/// Translate every function of the plan (callees first) and write the outputs.
pub fn reduce(elf: &Elf, plan: &Plan, elf_path: &str, outdir: &Path) -> Result<Output> {
    let elf_name = Path::new(elf_path)
        .file_name()
        .unwrap()
        .to_string_lossy()
        .into_owned();
    let mut names = BTreeMap::new();
    for f in &plan.functions {
        let a = elf
            .symbols
            .iter()
            .find(|s| s.0 == f.name)
            .ok_or_else(|| format_err!("no symbol {}", f.name))?
            .1;
        names.insert(a, f.name.clone());
    }
    let specs: BTreeMap<String, &FnSpec> =
        plan.functions.iter().map(|f| (f.name.clone(), f)).collect();
    let mut an: BTreeMap<String, Analysis> = BTreeMap::new();
    for f in &plan.functions {
        an.insert(f.name.clone(), analyse(elf, &f.name, &names)?);
    }
    // callee-first order; recursion is rejected
    let mut order: Vec<String> = vec![];
    let mut state: BTreeMap<String, u8> = BTreeMap::new();
    fn visit(
        n: &str,
        an: &BTreeMap<String, Analysis>,
        st: &mut BTreeMap<String, u8>,
        order: &mut Vec<String>,
    ) -> Result<()> {
        match st.get(n) {
            Some(2) => return Ok(()),
            Some(1) => bail!("recursion through {n} is not supported"),
            _ => {}
        }
        st.insert(n.into(), 1);
        for g in an[n].callees.values() {
            visit(g, an, st, order)?;
        }
        st.insert(n.into(), 2);
        order.push(n.into());
        Ok(())
    }
    for f in &plan.functions {
        visit(&f.name, &an, &mut state, &mut order)?;
    }
    let called: BTreeSet<String> = an
        .values()
        .flat_map(|a| a.callees.values().cloned())
        .collect();
    let mut sigs: BTreeMap<String, Sig> = BTreeMap::new();
    for n in &order {
        let a = an.get_mut(n).unwrap();
        dataflow(a, &sigs);
        let sig = signature(a, called.contains(n));
        sigs.insert(n.clone(), sig);
    }
    let mut modules = BTreeMap::new();
    for n in &order {
        modules.insert(
            n.clone(),
            emit_module(&an[n], specs[n], plan, &sigs, &specs, &elf_name)?,
        );
    }
    // files
    let sha = fnv(&std::fs::read(elf_path)?);
    std::fs::create_dir_all(outdir.join("modules"))?;
    for (n, m) in &modules {
        std::fs::write(outdir.join("modules").join(format!("{n}.wat")), m)?;
        let a = &an[n];
        let sp = specs[n];
        let cs: BTreeSet<&String> = a.callees.values().collect();
        let assumes: Vec<String> = cs
            .iter()
            .map(|g| {
                format!(
                    "{{\"import\": {}, \"requires\": {}, \"ensures\": {}}}",
                    js(g),
                    js(&specs[*g].requires),
                    js(&specs[*g].ensures)
                )
            })
            .collect();
        let dir = outdir.join("pieces/ag").join(n);
        std::fs::create_dir_all(&dir)?;
        let words: String =
            a.f.insts
                .iter()
                .map(|(_, w, _)| format!("{w:08x}"))
                .collect::<Vec<_>>()
                .join("");
        let piece = format!(
            "{{\n  \"schema\": \"silmaril.wasm-sim.piece.v0\",\n  \"id\": {},\n  \"kind\": \"assume-guarantee\",\n  \"function\": {},\n  \"address\": \"{:#x}\",\n  \"words\": \"{words}\",\n  \"program\": {{\"kind\": \"annotated-wat\", \"source\": \"../../../modules/{n}.wat\", \"representation\": \"P-locals\", \"imports\": {{\"callees\": [{}], \"memory\": {}}}, \"params\": [{}], \"results\": [{}]}},\n  \"spec\": {{\"requires\": {}, \"ensures\": {}, \"reads\": {}, \"writes\": {}, \"assumes\": [{}]}},\n  \"statement\": {},\n  \"solvers\": [\"wpc/HWP (Silmaril.Wasm.Logic.Core)\", \"wasm-vc (i64)\", \"agent\"],\n  \"status\": \"open\"\n}}\n",
            js(&format!("{}/ag/{n}", plan.id)),
            js(n),
            a.f.base,
            cs.iter().map(|g| js(g)).collect::<Vec<_>>().join(", "),
            a.uses_mem || !cs.is_empty(),
            sigs[n]
                .params
                .iter()
                .map(|&r| js(ABI[r as usize]))
                .collect::<Vec<_>>()
                .join(", "),
            sigs[n]
                .results
                .iter()
                .map(|&r| js(ABI[r as usize]))
                .collect::<Vec<_>>()
                .join(", "),
            js(&sp.requires),
            js(&sp.ensures),
            js(&format!("{:?}", sp.reads)),
            js(&format!("{:?}", sp.writes)),
            assumes.join(", "),
            js(&format!(
                "assuming the imports {cs:?} meet their contracts, the Wasm function `{n}` meets its contract (total correctness, ABI checks at ret)"
            )),
        );
        std::fs::write(dir.join("piece.json"), piece)?;
    }
    // dag.json: isa/f <= wasm/f + tv/f ; wasm/f <= ag/f + wasm/g for callees g
    let mut nodes = vec![];
    let mut edges = vec![];
    for n in &order {
        let cs: BTreeSet<&String> = an[n].callees.values().collect();
        nodes.push(format!("{{\"id\": \"isa/{n}\", \"kind\": \"isa-problem\", \"status\": \"open\", \"statement\": {}}}", js(&format!("Silmaril.RiscV.Ext.MState.step from the entry of `{n}` with the plan contract (+ ABI) reaches the return address"))));
        nodes.push(format!("{{\"id\": \"wasm/{n}\", \"kind\": \"wasm-problem\", \"status\": \"open\", \"statement\": {}}}", js(&format!("the linked Wasm modules of `{n}` and its callees meet the contract of `{n}`"))));
        let lean_ref = specs[n]
            .lean
            .as_ref()
            .map(|l| format!(", \"lean\": \"Silmaril.WasmSpec.{}.Spec\"", l.0))
            .unwrap_or_default();
        nodes.push(format!("{{\"id\": \"ag/{n}\", \"kind\": \"wasm-piece\", \"status\": \"open\"{lean_ref}, \"files\": [\"modules/{n}.wat\", \"pieces/ag/{n}/piece.json\"]}}"));
        nodes.push(format!("{{\"id\": \"tv/{n}\", \"kind\": \"translation-validation\", \"status\": \"open\", \"statement\": {}}}", js(&format!("modules/{n}.wat simulates the words of `{n}`: per-instruction method soundness (P-locals snippets = Ext.Instr.exec), structuring of the CFG, calls = ABI calls of the imported callees"))));
        edges.push(format!("{{\"goal\": \"isa/{n}\", \"pieces\": [\"wasm/{n}\", \"tv/{n}\"], \"status\": \"task\", \"note\": \"transfer (reduction.toml)\"}}"));
        let mut ps = vec![format!("\"ag/{n}\"")];
        ps.extend(cs.iter().map(|g| format!("\"wasm/{g}\"")));
        edges.push(format!("{{\"goal\": \"wasm/{n}\", \"pieces\": [{}], \"status\": \"task\", \"note\": \"assume-guarantee over the acyclic call graph (Silmaril.Sim.Reduce.ag_compose)\"}}", ps.join(", ")));
    }
    let dag = format!(
        "{{\n  \"schema\": \"silmaril.wasm-sim.dag.v0\",\n  \"id\": {},\n  \"title\": {},\n  \"root\": \"isa/{}\",\n  \"artifact\": {{\"elf\": {}, \"source\": {}, \"fnv1a64\": \"{sha:016x}\"}},\n  \"isa\": {{\"machine\": \"Silmaril.RiscV.Ext.MState.step\"}},\n  \"sim\": {{\"representation\": \"P-locals\", \"methods\": \"examples/wasm-sim/rv64/parts\"}},\n  \"nodes\": [\n    {}\n  ],\n  \"edges\": [\n    {}\n  ]\n}}\n",
        js(&plan.id),
        js(&plan.title),
        plan.root,
        js(&elf_name),
        js(&plan.source),
        nodes.join(",\n    "),
        edges.join(",\n    ")
    );
    std::fs::write(outdir.join("dag.json"), dag)?;
    let mut m = String::new();
    writeln!(
        m,
        "# Reduction manifest (tools/wasm-sim rv64 reduce): RV64 problems -> Wasm problems."
    )?;
    writeln!(
        m,
        "schema = 2\nplan = {}\nelf = {}\nelf_fnv1a64 = \"{sha:016x}\"\norder = {:?}",
        js(&plan.id),
        js(&elf_name),
        order
    )?;
    for n in &order {
        let a = &an[n];
        writeln!(
            m,
            "\n[[function]]\nname = {}\nentry = {:#x}\nmodule = \"modules/{n}.wat\"",
            js(n),
            a.f.base
        )?;
        writeln!(
            m,
            "words = [{}]",
            a.f.insts
                .iter()
                .map(|(_, w, _)| format!("{w:#010x}"))
                .collect::<Vec<_>>()
                .join(", ")
        )?;
        writeln!(
            m,
            "params = {:?}\nresults = {:?}",
            sigs[n]
                .params
                .iter()
                .map(|&r| ABI[r as usize])
                .collect::<Vec<_>>(),
            sigs[n]
                .results
                .iter()
                .map(|&r| ABI[r as usize])
                .collect::<Vec<_>>()
        )?;
        writeln!(
            m,
            "callees = {:?}\nabi_checked = {:?}",
            a.callees.values().collect::<BTreeSet<_>>(),
            checked(a)
                .iter()
                .map(|&r| ABI[r as usize])
                .collect::<Vec<_>>()
        )?;
        let groups: BTreeSet<&str> = a.f.insts.iter().map(|(_, _, i)| i.group).collect();
        writeln!(m, "simulator_groups = {:?}", groups)?;
    }
    writeln!(
        m,
        r#"
transfer = """
For each function f: if the Wasm function `f` (modules/f.wat, linked with the
modules of its callees and a memory) meets its contract for all arguments, i.e.
from params satisfying @requires it returns normally with results satisfying
@ensures, then for every RV64 state s with pc = entry(f), the words of f (and
its callees) fetchable at their entries, memory below 2^32 equal to the Wasm
memory, the param registers holding the Wasm arguments and ra = any four-byte-
aligned return address r outside the code, Ext.MState.step retires finitely many
instructions reaching pc = r with the result registers equal to the Wasm results,
ra and the callee-saved registers restored, and memory equal to the final Wasm
memory. Traps of the Wasm function (misaligned/out-of-memory access, ABI check
failure, misaligned target) correspond to RV faults or ABI violations, which the
total-correctness contract excludes. Composition: assume-guarantee over the
acyclic call graph (dag.json); per-function translation validity (tv/f) is the
per-instruction method soundness plus CFG structuring."""
"#
    )?;
    std::fs::write(outdir.join("reduction.toml"), m)?;
    let entries = an.iter().map(|(n, a)| (n.clone(), a.f.base)).collect();
    let callees = an
        .iter()
        .map(|(n, a)| {
            (
                n.clone(),
                a.callees
                    .values()
                    .cloned()
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .collect(),
            )
        })
        .collect();
    Ok(Output {
        modules,
        sigs,
        order,
        entries,
        callees,
    })
}

pub fn fnv(b: &[u8]) -> u64 {
    b.iter().fold(0xcbf29ce484222325u64, |h, &x| {
        (h ^ x as u64).wrapping_mul(0x100000001b3)
    })
}

/// What `check` returns: (returning runs, faults in both, skipped (fuel), the returning runs
/// as (function, arguments, results)).
pub type CheckReport = (u64, u64, u64, Vec<(String, Vec<u64>, Vec<u64>)>);

/// Runtime check of a reduction, for every function of the plan: the linked
/// Wasm modules and the simulator (`full`, G) started at the function entry
/// with ra = sentinel agree on the result registers and on the whole memory
/// (or both fault), for the plan's tests and random arguments.
/// Returns (agreeing runs that return, agreeing runs that fault, runs skipped for lack of fuel).
/// Also returns, for functions without memory, up to 30 returning runs `(function, params, results)`
/// for the contract consistency check (`consistency`).
pub fn check(elf: &Elf, plan: &Plan, out: &Output, samples: u64) -> Result<CheckReport> {
    use super::host::{self, SENTINEL, STACK_TOP, Sim};
    use wasmtime::*;
    let engine = host::engine();
    let simm = Module::new(
        &engine,
        super::asm::build(&super::asm::Config::new(super::asm::State::G, "full"), ""),
    )?;
    let memm = host::mem_module(&engine)?;
    let mut fcfg = Config::new();
    fcfg.consume_fuel(true);
    let fengine = Engine::new(&fcfg)?;
    let mut wmods = BTreeMap::new();
    for (n, w) in &out.modules {
        wmods.insert(n.clone(), Module::new(&fengine, w)?);
    }
    let mut r = super::randprog::Rng::new(11);
    let mut buf = vec![0u8; BUF_LEN];
    for b in buf.iter_mut() {
        *b = r.next_u64() as u8;
    }
    let (mut ok, mut faults, mut skipped) = (0, 0, 0);
    let mut runs = vec![];
    for f in &plan.functions {
        let n = &f.name;
        let sig = &out.sigs[n];
        // callees in dependency order
        let mut deps: Vec<String> = vec![];
        let mut todo = vec![n.clone()];
        while let Some(x) = todo.pop() {
            for g in &out.callees[&x] {
                if !deps.contains(g) {
                    deps.push(g.clone());
                    todo.push(g.clone());
                }
            }
        }
        let deps: Vec<&String> = out.order.iter().filter(|x| deps.contains(x)).collect();
        let mut vectors: Vec<Vec<Arg>> = f.tests.clone();
        for _ in 0..samples {
            vectors.push(
                (10..=17)
                    .map(|reg| {
                        if f.pointers.contains(&reg) {
                            Arg::Buf(8 * r.below(64))
                        } else {
                            Arg::Int(match f.sample_max {
                                Some(m) => r.below(m + 1),
                                None => {
                                    if r.below(2) == 0 {
                                        r.below(100)
                                    } else {
                                        r.value()
                                    }
                                }
                            })
                        }
                    })
                    .collect(),
            );
        }
        for (k, args) in vectors.iter().enumerate() {
            let mut s = Sim::new(&engine, &simm, &memm)?;
            s.load_elf(elf)?;
            s.env.data_mut(&mut s.store)[BUF as usize..BUF as usize + BUF_LEN]
                .copy_from_slice(&buf);
            for (i, a) in args.iter().enumerate().take(8) {
                s.set(
                    10 + i as i32,
                    match a {
                        Arg::Int(v) => *v,
                        Arg::Buf(o) => BUF + o,
                    },
                );
            }
            s.set(1, SENTINEL);
            s.set(2, STACK_TOP);
            s.set(32, out.entries[n]);
            let init = s.regs();
            let (st, _) = s.run(10_000_000);
            if st == 4 {
                skipped += 1;
                continue;
            }
            let halted = st == 1 && s.get(32) == SENTINEL;
            // Wasm side
            let mut store = Store::new(&fengine, ());
            store.set_fuel(2_000_000_000)?;
            let mem = Memory::new(&mut store, MemoryType::new(1024, Some(1024)))?;
            {
                let d = mem.data_mut(&mut store);
                for seg in &elf.segments {
                    d[seg.vaddr as usize..seg.vaddr as usize + seg.data.len()]
                        .copy_from_slice(&seg.data);
                }
                d[BUF as usize..BUF as usize + BUF_LEN].copy_from_slice(&buf);
            }
            let mut linker = Linker::new(&fengine);
            linker.define(&mut store, "env", "memory", mem)?;
            for d in &deps {
                let inst = linker.instantiate(&mut store, &wmods[*d])?;
                linker.instance(&mut store, d, inst)?;
            }
            let inst = linker.instantiate(&mut store, &wmods[n])?;
            let func = inst.get_func(&mut store, n).unwrap();
            let params: Vec<Val> = sig
                .params
                .iter()
                .map(|&p| Val::I64(init[p as usize] as i64))
                .collect();
            let mut res = vec![Val::I64(0); sig.results.len()];
            let wr = func.call(&mut store, &params, &mut res);
            let agree = match (&wr, halted) {
                (Ok(()), true) => {
                    let regs = s.regs();
                    sig.results
                        .iter()
                        .zip(&res)
                        .all(|(&reg, v)| v.unwrap_i64() as u64 == regs[reg as usize])
                        && mem.data(&store)[..] == s.env.data(&s.store)[..]
                }
                (Err(_), false) => true,
                _ => false,
            };
            if !agree {
                bail!(
                    "{n}: vector {k} {args:?}: simulator status {st} regs {:x?}; Wasm {:?} {:x?}",
                    s.regs(),
                    wr.err().map(|e| e.to_string()),
                    res.iter().map(|v| v.unwrap_i64()).collect::<Vec<_>>()
                );
            }
            if halted {
                ok += 1;
                if !out.modules[n].contains("(import \"env\" \"memory\"")
                    && runs
                        .iter()
                        .filter(|x: &&(String, Vec<u64>, Vec<u64>)| &x.0 == n)
                        .count()
                        < 30
                {
                    runs.push((
                        n.clone(),
                        params.iter().map(|v| v.unwrap_i64() as u64).collect(),
                        res.iter().map(|v| v.unwrap_i64() as u64).collect(),
                    ));
                }
            } else {
                faults += 1
            }
        }
    }
    Ok((ok, faults, skipped, runs))
}
