//! `wasm-sim elfv`: functions cut out of real ELF executables, run natively and through a stack
//! of increasingly abstract Wasm layers, with the adjacent-layer equivalence problems emitted
//! for `wasm-vc solve` (see `docs/projects/wasm-sim-abi.md` for the simulator interface).
//!
//! Layers (each a closed core module exporting the same System V wrapper `f`, see `wrapper`):
//!
//! * `L0` P-mem: the decoding G simulator (`decode.wat` `step`) fetching the ELF's `.text` bytes
//!   from its own memory (data segment) — the bytes are the program;
//! * `L1` P-calls: the P-calls translation of the decoded function over the same G methods;
//! * `L2` L-form: `L1` with every method inlined (binaryen) and the G globals turned into locals
//!   of the wrapper (`localize`);
//! * `L3` optimized: `wasm-opt -O3` of `L2`;
//! * `L4` spec: a hand-written Wasm function over C types plus a generated ABI adapter.
//!
//! The wrapper's interface: parameters `rax rcx rdx rbx rbp rsi rdi r8 .. r15` (15 GPRs, rsp is
//! fixed) and `cf pf af zf sf of` (bit 0), result `rax`. It traps unless the run returns to the
//! sentinel with `rsp + 8` and `rbx rbp r12-r15` preserved (AbiReturn).

use super::difftest::{self, Arg, Rng};
use super::native::{Native, State};
use super::pcalls::{Opts, decode_all, translate_func};
use crate::harness::{self, Host, PageMem, Undef};
use crate::reduce::elf::Elf;
use anyhow::{Context, Result, anyhow, bail};
use serde::Deserialize;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;
use wasmtime::{Linker, Module, Store, Val};

/// Guest address of the copied `.text` (inside the 64 KiB window of `mem-local.wat`).
pub const TEXT_BASE: u64 = 0x108000;
/// Entry `rsp` (8 mod 16, as at a System V entry); the return address slot.
pub const STACK: u64 = 0x10eff8;
pub const SENTINEL: u64 = 0xFFFF_FFFF_FFFF_F000;
/// Wrapper parameters: GPR location numbers (no rsp), then flag locations.
pub const PREGS: [i32; 15] = [0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
pub const PFLAGS: [i32; 6] = [17, 18, 19, 20, 21, 22];
pub const LAYERS: [&str; 5] = ["L0", "L1", "L2", "L3", "L4"];

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Targets {
    schema: String,
    #[serde(default)]
    defs: BTreeMap<String, String>,
    #[serde(rename = "elf")]
    elfs: Vec<ElfT>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ElfT {
    name: String,
    path: String,
    /// Wasm spec module (WAT, a sequence of fields) for this ELF's functions.
    #[serde(default)]
    spec: Option<String>,
    #[serde(rename = "function")]
    functions: Vec<FnT>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct FnT {
    name: String,
    /// argument kinds: any | small:N | nonzero
    args: Vec<String>,
    /// C signature `ret(arg, ...)` over u32 i32 u64 i64 (the spec function's types)
    #[serde(default)]
    sig: Option<String>,
    #[serde(default = "tru")]
    requires: String,
    #[serde(default = "tru")]
    ensures: String,
    /// x86 loops: unroll bound for the solver problems
    #[serde(default)]
    unroll: Option<u32>,
}

fn tru() -> String {
    "true".into()
}

#[derive(clap::Args)]
pub struct Args {
    /// targets (`silmaril.wasm-sim.elfv.v0`)
    targets: PathBuf,
    /// output directory
    #[arg(long, short)]
    out: PathBuf,
    #[arg(long, default_value_t = 300)]
    per: usize,
    #[arg(long, default_value_t = 1)]
    seed: u64,
    /// only these functions
    #[arg(long, value_delimiter = ',')]
    only: Vec<String>,
    /// skip the binaryen layers (L2, L3)
    #[arg(long)]
    no_opt: bool,
}

/// Buffer area: native `dbase + NBUF`, guest `WBUF` (both `ABUF` bytes).
pub const NBUF: usize = 0x2800;
pub const WBUF: u64 = 0x101000;
pub const ABUF: usize = 0x1000;

/// Argument kinds: a value (`any`, `small:N`, `nonzero`), a pointer to offset `o` of the
/// buffer area (`buf:o`; the area is random), the same after copying `0x400` bytes from offset
/// `src` and changing one of them half of the time (`copy:o:src`), or a NUL-terminated string
/// of random length at `o` (`str:o`).
#[derive(Clone, Copy)]
enum K {
    V(Arg),
    Buf(u64),
    Copy(u64, u64),
    Str(u64),
}

fn parse_arg(s: &str) -> Result<K> {
    let p: Vec<&str> = s.split(':').collect();
    Ok(match p.as_slice() {
        ["any"] => K::V(Arg::Any),
        ["nonzero"] => K::V(Arg::NonZero),
        ["small", n] => K::V(Arg::Small(n.parse()?)),
        ["buf", o] => K::Buf(parse_u(o)?),
        ["copy", o, src] => K::Copy(parse_u(o)?, parse_u(src)?),
        ["str", o] => K::Str(parse_u(o)?),
        _ => bail!("unknown argument kind {s}"),
    })
}

fn parse_u(s: &str) -> Result<u64> {
    Ok(match s.strip_prefix("0x") {
        Some(h) => u64::from_str_radix(h, 16)?,
        None => s.parse()?,
    })
}

/// (native values, guest values) of the arguments, filling the buffer area.
fn gen_args(rng: &mut Rng, kinds: &[K], dbase: u64, area: &mut [u8]) -> (Vec<u64>, Vec<u64>) {
    let (mut nv, mut wv) = (vec![], vec![]);
    for k in kinds {
        let (n, w) = match *k {
            K::V(a) => {
                let v = difftest::gen_args(rng, &[a], dbase, &mut [])[0];
                (v, v)
            }
            K::Buf(o) => (dbase + NBUF as u64 + o, WBUF + o),
            K::Copy(o, src) => {
                let (o, src) = (o as usize, src as usize);
                for i in 0..0x400 {
                    area[o + i] = area[src + i];
                }
                if rng.below(2) == 0 {
                    let j = o + rng.below(0x400) as usize;
                    area[j] = rng.next_u64() as u8;
                }
                (dbase + NBUF as u64 + o as u64, WBUF + o as u64)
            }
            K::Str(o) => {
                let len = rng.below(200) as usize;
                for i in 0..len {
                    area[o as usize + i] = 1 + (rng.next_u64() % 255) as u8;
                }
                area[o as usize + len] = 0;
                (dbase + NBUF as u64 + o, WBUF + o)
            }
        };
        nv.push(n);
        wv.push(w);
    }
    (nv, wv)
}

/// The bytes and symbol of a function in an ELF's `.text`.
pub struct Cut {
    pub text_addr: u64,
    pub text: Vec<u8>,
    pub addr: u64,
    pub size: u64,
}

pub fn cut(elf: &Elf, name: &str) -> Result<Cut> {
    let (text_addr, text) = elf.text()?;
    let s = elf.symbol(name)?;
    if !s.is_func || s.value < text_addr || s.value + s.size > text_addr + text.len() as u64 {
        bail!("{name} is not a function symbol in .text");
    }
    Ok(Cut {
        text_addr,
        text: text.to_vec(),
        addr: s.value,
        size: s.size,
    })
}

impl Cut {
    pub fn bytes(&self) -> &[u8] {
        let o = (self.addr - self.text_addr) as usize;
        &self.text[o..o + self.size as usize]
    }
    /// Entry address in the guest layout of the layers.
    pub fn entry(&self) -> u64 {
        TEXT_BASE + (self.addr - self.text_addr)
    }
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn data_segment(text: &[u8]) -> String {
    let s: String = text.iter().map(|b| format!("\\{b:02x}")).collect();
    format!(
        "  ;; the ELF's .text, copied to guest {TEXT_BASE:#x}\n  (data (i32.const {}) \"{s}\")\n",
        TEXT_BASE - 0x100000
    )
}

/// The System V wrapper `f`; `body` runs the function (and leaves the state in the globals).
fn wrapper(name: &str, entry: u64, body: &str) -> String {
    let mut w = String::new();
    let params: String = PREGS
        .iter()
        .chain(PFLAGS.iter())
        .map(|&l| format!(" (param ${} i64)", super::NAMES[l as usize]))
        .collect();
    let _ = writeln!(
        w,
        "  ;; System V wrapper for `{name}`: entry rsp = {STACK:#x} holding the sentinel; traps unless AbiReturn."
    );
    let _ = writeln!(w, "  (func $wrap (export \"f\"){params} (result i64)");
    let _ = writeln!(w, "    (local $st i32) (local $fuel i64)");
    for &l in &PREGS {
        let _ = writeln!(
            w,
            "    (call $set (i32.const {l}) (local.get ${}))",
            super::NAMES[l as usize]
        );
    }
    for &l in &PFLAGS {
        let _ = writeln!(
            w,
            "    (call $set (i32.const {l}) (i64.and (local.get ${}) (i64.const 1)))",
            super::NAMES[l as usize]
        );
    }
    let _ = writeln!(w, "    (call $set (i32.const 23) (i64.const 0))");
    let _ = writeln!(w, "    (call $set (i32.const 4) (i64.const {STACK}))");
    let _ = writeln!(
        w,
        "    (call $store64 (i64.const {STACK}) (i64.const {}))",
        SENTINEL as i64
    );
    let _ = writeln!(w, "    (call $set (i32.const 16) (i64.const {entry}))");
    w += body;
    let _ = writeln!(
        w,
        "    (if (i64.ne (call $get (i32.const 16)) (i64.const {})) (then (unreachable)))",
        SENTINEL as i64
    );
    let _ = writeln!(
        w,
        "    (if (i64.ne (call $get (i32.const 4)) (i64.const {})) (then (unreachable)))",
        STACK + 8
    );
    for l in super::problem::CALLEE_SAVED {
        let _ = writeln!(
            w,
            "    (if (i64.ne (call $get (i32.const {l})) (local.get ${})) (then (unreachable)))",
            super::NAMES[l as usize]
        );
    }
    let _ = writeln!(w, "    (call $get (i32.const 0)))");
    w
}

fn common(decoder: bool) -> Result<String> {
    Ok(format!(
        "{}{}{}{}{}",
        super::src("header.wat")?,
        super::src("mem-local.wat")?,
        super::src("state-g.wat")?,
        super::src("core.wat")?,
        if decoder {
            super::src("decode.wat")?
        } else {
            String::new()
        }
    ))
}

/// L0: P-mem (decoder over the bytes in memory).
pub fn layer0(name: &str, c: &Cut) -> Result<String> {
    let body = "    (local.set $fuel (i64.const 100000000))
    (block $done (loop $l
      (local.set $st (call $step))
      (br_if $done (i32.eq (local.get $st) (i32.const 1)))
      (if (i32.ne (local.get $st) (i32.const 0)) (then (unreachable)))
      (local.set $fuel (i64.sub (local.get $fuel) (i64.const 1)))
      (br_if $l (i64.ne (local.get $fuel) (i64.const 0)))
      (unreachable)))\n";
    let text = format!(
        ";; L0 (P-mem) for `{name}` (GENERATED by `wasm-sim elfv`): the G decoding simulator runs the ELF bytes.\n{}{}{})\n",
        common(true)?,
        data_segment(&c.text),
        wrapper(name, c.entry(), body)
    );
    Ok(super::prune::prune(&text, &["$wrap"]))
}

/// L1: P-calls translation of the function (and its callees in `.text`).
pub fn layer1(name: &str, c: &Cut) -> Result<String> {
    let funcs = decode_all(&c.text, TEXT_BASE, &[c.entry()])?;
    let mut used = BTreeSet::new();
    let mut prog = String::new();
    for f in &funcs {
        prog += &translate_func(f, &Opts::default(), &mut used)?;
    }
    let body = format!(
        "    (if (i32.ne (call $f_{:x}) (i32.const 0)) (then (unreachable)))\n",
        c.entry()
    );
    let text = format!(
        ";; L1 (P-calls) for `{name}` (GENERATED by `wasm-sim elfv`): method calls of the decoded bytes.\n{}{}  ;; ---- program\n{prog}{})\n",
        common(false)?,
        data_segment(&c.text),
        wrapper(name, c.entry(), &body)
    );
    Ok(super::prune::prune(&text, &["$wrap"]))
}

/// The L0 ⊑ L1 link, decomposed per instruction: for every decoded instruction at `a`, the
/// decoder's `step` at rip = a (I0) and the P-calls translation of that one instruction (I1),
/// from the same arbitrary state (registers, flags, memory with the code bytes kept), reach
/// equal states. Returns (I0 text, I1 text, problems (addr, toml)).
/// The per-instruction link: (I0 text, I1 text, problems (addr, toml)).
pub type InsnTv = (String, String, Vec<(u64, String)>);

pub fn insn_tv(name: &str, c: &Cut) -> Result<InsnTv> {
    let funcs = decode_all(&c.text, TEXT_BASE, &[c.entry()])?;
    let mut used = BTreeSet::new();
    let mut prog = String::new();
    for f in &funcs {
        prog += &translate_func(f, &Opts::default(), &mut used)?;
    }
    // per instruction: the comment `;; 0x…: asm` then one line of method calls
    let lines: Vec<&str> = prog.lines().collect();
    let mut steps = String::new();
    let mut calls = String::new();
    let mut probs = vec![];
    let mut roots: Vec<String> = vec![];
    for (k, l) in lines.iter().enumerate() {
        let t = l.trim_start();
        let Some(rest) = t.strip_prefix(";; 0x") else {
            continue;
        };
        let Some((addr, asm)) = rest.split_once(": ") else {
            continue;
        };
        let a = u64::from_str_radix(addr, 16)?;
        let mut body = lines
            .get(k + 1)
            .context("instruction line")?
            .trim()
            .to_string();
        // control flow inside the dispatcher becomes a return
        while let Some(p) = body.find("(local.set $b (i32.const ") {
            let e = body[p..]
                .find("(br $d)")
                .map(|q| p + q + "(br $d)".len())
                .context("br $d")?;
            body.replace_range(p..e, "(return (i32.const 0))");
        }
        let _ = writeln!(
            steps,
            "  ;; {addr}: {asm}\n  (func $s_{a:x} (export \"s_{a:x}\") (result i32)\n    (call $set (i32.const 16) (i64.const {a}))\n    (call $step))"
        );
        let _ = writeln!(
            calls,
            "  ;; {addr}: {asm}\n  (func $s_{a:x} (export \"s_{a:x}\") (result i32) (local $s i32)\n    (call $set (i32.const 16) (i64.const {a}))\n    {body}\n    (i32.const 0))"
        );
        roots.push(format!("$s_{a:x}"));
        let keep = format!("m0:{:#x}:{}", TEXT_BASE - 0x100000, c.text.len());
        let mut t = format!(
            "# L0 ⊑ L1 for one instruction of `{name}` ({addr}: {asm}), GENERATED by `wasm-sim elfv`:\n\
             # the decoder's step on the ELF bytes vs. the P-calls method calls, from the same arbitrary\n\
             # state (code bytes kept): equal status, traps, GPRs, rip, CF PF ZF SF OF, memory.\n\
             # AF is not compared (undefined after logic ops: an nd.undef answer, fresh per side).\n\
             name = \"{name}-insn-{a:x}\"\nkind = \"equiv\"\ninit = \"symbolic\"\nobserve = [\"result\", \"trap\", \"map\", \"memory\"]\n\
             [a]\nmodules = [{{ name = \"m\", wat = \"I0.wat\" }}]\nentry = \"s_{a:x}\"\nkeep = [\"{keep}\"]\n\
             [b]\nmodules = [{{ name = \"m\", wat = \"I1.wat\" }}]\nentry = \"s_{a:x}\"\nkeep = [\"{keep}\"]\n"
        );
        for (i, n) in super::NAMES[..23]
            .iter()
            .enumerate()
            .filter(|(_, n)| **n != "af")
        {
            let g = if i < 16 {
                format!("r{i}")
            } else {
                n.to_string()
            };
            let _ = writeln!(t, "[[map]]\nname = \"{n}\"\na = \"g:{g}\"\nb = \"g:{g}\"");
        }
        probs.push((a, t));
    }
    let rr: Vec<&str> = roots.iter().map(|s| s.as_str()).collect();
    let i0 = format!(
        ";; I0: the decoding step at each instruction of `{name}` (GENERATED by `wasm-sim elfv`).\n{}{}{steps})\n",
        common(true)?,
        data_segment(&c.text)
    );
    let i1 = format!(
        ";; I1: the P-calls method calls of each instruction of `{name}` (GENERATED by `wasm-sim elfv`).\n{}{}{calls})\n",
        common(false)?,
        data_segment(&c.text)
    );
    Ok((
        super::prune::prune(&i0, &rr),
        super::prune::prune(&i1, &rr),
        probs,
    ))
}

fn run_tool(cmd: &mut Command) -> Result<()> {
    let o = cmd.output().with_context(|| format!("running {cmd:?}"))?;
    if !o.status.success() {
        bail!("{cmd:?} failed: {}", String::from_utf8_lossy(&o.stderr));
    }
    Ok(())
}

/// Inline everything into the wrapper (binaryen), print as WAT.
fn inline_all(l1_wasm: &Path, out_wat: &Path) -> Result<()> {
    run_tool(
        Command::new("wasm-opt")
            .arg(l1_wasm)
            .args([
                "-g",
                "--enable-bulk-memory",
                "--enable-sign-ext",
                "--inline-functions-with-loops",
                "--always-inline-max-function-size=1000000",
                "--flexible-inline-max-function-size=1000000",
                "--one-caller-inline-max-function-size=1000000",
                "--inlining",
                "--remove-unused-module-elements",
                "-S",
                "-o",
            ])
            .arg(out_wat),
    )
}

/// Globals → locals of the single remaining function: valid when the module has one function
/// that is the only reader/writer of the (unexported) mutable globals and is not re-entered
/// (checked afterwards by the L1 ≡ L2 problem, not assumed).
pub fn localize(wat: &str) -> Result<String> {
    let nfunc = wat
        .lines()
        .filter(|l| l.trim_start().starts_with("(func "))
        .count();
    if nfunc != 1 {
        bail!("localize: {nfunc} functions after inlining (expected 1)");
    }
    let mut globals: Vec<(String, String)> = vec![];
    let mut out = String::new();
    for l in wat.lines() {
        let t = l.trim_start();
        if t.starts_with("(global $") && t.contains("(mut ") {
            let name = t["(global ".len()..]
                .split_whitespace()
                .next()
                .unwrap()
                .to_string();
            let ty = t
                .split("(mut ")
                .nth(1)
                .unwrap()
                .split(')')
                .next()
                .unwrap()
                .to_string();
            globals.push((name, ty));
            continue;
        }
        out += l;
        out.push('\n');
    }
    for (g, _) in &globals {
        if out.contains(&format!("(export \"{}\" (global {g}", &g[1..])) {
            bail!("localize: global {g} is exported");
        }
    }
    let mut res = String::new();
    let mut in_func = false;
    let mut declared = false;
    for l in out.lines() {
        let t = l.trim_start();
        if t.starts_with("(func ") {
            in_func = true;
        }
        let mut line = l.to_string();
        for (g, _) in &globals {
            let lg = format!("$g_{}", &g[1..]);
            for (from, to) in [("global.get", "local.get"), ("global.set", "local.set")] {
                for end in [")", " ", ""] {
                    let pat = format!("({from} {g}{end}");
                    if end.is_empty() && !line.trim_end().ends_with(&pat) {
                        continue;
                    }
                    line = line.replace(&pat, &format!("({to} {lg}{end}"));
                }
            }
        }
        // declare the locals before the first non-header line of the function
        if in_func
            && !declared
            && !(t.starts_with("(func ")
                || t.starts_with("(param")
                || t.starts_with("(result")
                || t.starts_with("(local ")
                || t.starts_with("(type"))
        {
            for (g, ty) in &globals {
                res += &format!("  (local $g_{} {ty})\n", &g[1..]);
            }
            declared = true;
        }
        res += &line;
        res.push('\n');
    }
    for (g, _) in &globals {
        if res.contains(&format!("global.get {g}")) || res.contains(&format!("global.set {g}")) {
            bail!("localize: {g} still used as a global");
        }
    }
    Ok(res)
}

/// The ABI adapter of the spec: `f` with the wrapper's interface calling `$<name>`. Types:
/// `u32 i32 int` (low 32 bits), `u64 i64` (64 bits), `size` (low 32 bits), `ptr` (guest address
/// ↔ offset in the spec's memory, which maps the window `[0x100000, 0x110000)` like the layers').
/// With a memory, the adapter also stores the sentinel return address at the entry `rsp`, as
/// the caller does in the other layers.
fn adapter(name: &str, sig: &str, memory: bool) -> Result<String> {
    let (ret, args) = sig.split_once('(').context("sig: ret(args)")?;
    let args: Vec<&str> = args
        .trim_end_matches(')')
        .split(',')
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .collect();
    let regs = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"];
    let mut call = format!("(call ${name}");
    for (i, a) in args.iter().enumerate() {
        let r = regs[i];
        call += &match *a {
            "u32" | "i32" | "int" | "size" => format!(" (i32.wrap_i64 (local.get ${r}))"),
            "u64" | "i64" | "long" => format!(" (local.get ${r})"),
            "ptr" => format!(" (i32.wrap_i64 (i64.sub (local.get ${r}) (i64.const 0x100000)))"),
            t => bail!("unsupported argument type {t}"),
        };
    }
    call.push(')');
    let body = match ret.trim() {
        "u32" | "i32" | "int" | "size" => format!("(i64.extend_i32_u {call})"),
        "u64" | "i64" | "long" => call,
        "ptr" => format!("(i64.add (i64.extend_i32_u {call}) (i64.const 0x100000))"),
        t => bail!("unsupported result type {t}"),
    };
    let store = if memory {
        format!(
            "(i64.store (i32.const {}) (i64.const {}))\n    ",
            STACK - 0x100000,
            SENTINEL as i64
        )
    } else {
        String::new()
    };
    let params: String = PREGS
        .iter()
        .chain(PFLAGS.iter())
        .map(|&l| format!(" (param ${} i64)", super::NAMES[l as usize]))
        .collect();
    Ok(format!(
        "  ;; ABI adapter (GENERATED): rax = the C result of `{name}{}`\n  (func $wrap (export \"f\"){params} (result i64)\n    {store}{body})\n",
        &sig[ret.len()..]
    ))
}

/// Instantiate a closed layer module with the environment (nd.undef mode `u`).
fn instantiate(
    engine: &wasmtime::Engine,
    m: &Module,
    u: Undef,
) -> Result<(Store<Host>, wasmtime::Func, Option<wasmtime::Memory>)> {
    let mut h = Host::new(Box::new(PageMem::default()));
    h.undef = u;
    let mut store = Store::new(engine, h);
    let mut linker = Linker::new(engine);
    harness::add_env(&mut linker)?;
    let i = linker
        .instantiate(&mut store, m)
        .map_err(|e| anyhow!("{e:?}"))?;
    let f = i.get_func(&mut store, "f").context("export f")?;
    let mem = i.get_memory(&mut store, "mem");
    Ok((store, f, mem))
}

/// Call a layer with the buffer area copied to guest `WBUF`: (Some(rax) or None on a trap,
/// the area afterwards; empty without a memory).
fn call_layer(
    engine: &wasmtime::Engine,
    m: &Module,
    u: Undef,
    args: &[u64],
    area: &[u8],
) -> Result<(Option<u64>, Vec<u8>)> {
    let (mut store, f, mem) = instantiate(engine, m, u)?;
    let off = (WBUF - 0x100000) as usize;
    if let Some(mem) = mem {
        mem.write(&mut store, off, area)?;
    }
    let ps: Vec<Val> = args.iter().map(|&v| Val::I64(v as i64)).collect();
    let mut res = [Val::I64(0)];
    let r = match f.call(&mut store, &ps, &mut res) {
        Ok(()) => Some(res[0].unwrap_i64() as u64),
        Err(_) => None,
    };
    let after = match mem {
        Some(mem) => mem.data(&store)[off..off + area.len()].to_vec(),
        None => vec![],
    };
    Ok((r, after))
}

/// Number of instructions (operators) in all function bodies.
fn count_instrs(wat: &str) -> usize {
    let Ok(bin) = wat::parse_str(wat) else {
        return 0;
    };
    let mut n = 0;
    for p in wasmparser::Parser::new(0).parse_all(&bin) {
        if let Ok(wasmparser::Payload::CodeSectionEntry(body)) = p
            && let Ok(mut r) = body.get_operators_reader()
        {
            while !r.eof() {
                if r.read().is_err() {
                    break;
                }
                n += 1;
            }
        }
    }
    n
}

// One field per section of the generated problem file.
#[allow(clippy::too_many_arguments)]
fn tv_problem(
    name: &str,
    fname: &str,
    la: &str,
    lb: &str,
    observe: &[&str],
    map: &[(String, String)],
    pre: &str,
    unroll: u32,
    init: &str,
    defines: &[String],
) -> String {
    let mut t = format!(
        "# {la} ⊑ {lb} for `{fname}` (GENERATED by `wasm-sim elfv`): same wrapper interface, every input\n\
         # (15 GPRs, 6 flag bits), every environment (nd.undef answers): equal {}.\n\
         name = \"{name}\"\nkind = \"equiv\"\ninit = \"{init}\"\nunroll = {unroll}\nobserve = [{}]\n",
        observe.join(", "),
        observe
            .iter()
            .map(|o| format!("\"{o}\""))
            .collect::<Vec<_>>()
            .join(", ")
    );
    if pre != "true" {
        let _ = writeln!(t, "pre = [\"{}\"]", pre.replace('"', "\\\""));
        if !defines.is_empty() {
            let _ = writeln!(t, "defines = [{}]", defines.join(", "));
        }
    }
    let _ = writeln!(
        t,
        "[a]\nmodules = [{{ name = \"m\", wat = \"{la}.wat\" }}]\nentry = \"f\"\n[b]\nmodules = [{{ name = \"m\", wat = \"{lb}.wat\" }}]\nentry = \"f\""
    );
    for (a, b) in map {
        let _ = writeln!(t, "[[map]]\na = \"{a}\"\nb = \"{b}\"");
    }
    t
}

/// Rename `(old (reg r))` in a contract to the wrapper's parameter names (wasm-vc binds named
/// parameters by name) and `(reg rax)` to `result0`.
fn contract_to_params(s: &str) -> String {
    let mut s = s.to_string();
    for &l in PREGS.iter().chain(PFLAGS.iter()) {
        let n = super::NAMES[l as usize];
        s = s.replace(&format!("(old (reg {n}))"), n);
    }
    s.replace("(reg rax)", "result0")
}

/// The same with positional parameter names `p<i>` (for problems whose first side may have lost
/// its parameter names, e.g. binaryen output).
fn contract_to_pidx(s: &str) -> String {
    let mut s = s.to_string();
    for (i, &l) in PREGS.iter().chain(PFLAGS.iter()).enumerate() {
        s = s.replace(
            &format!("(old (reg {}))", super::NAMES[l as usize]),
            &format!("p{i}"),
        );
    }
    s
}

pub fn main(a: Args) -> Result<()> {
    let tpath = &a.targets;
    let t: Targets = toml::from_str(&std::fs::read_to_string(tpath)?)
        .with_context(|| format!("parsing {}", tpath.display()))?;
    if t.schema != "silmaril.wasm-sim.elfv.v0" {
        bail!("schema {}", t.schema);
    }
    let base = tpath.parent().unwrap_or(Path::new("."));
    let engine = harness::engine();
    let sim_g = harness::load_module(&engine, &super::sim_path("g"))?;
    let sim_m = harness::load_module(&engine, &super::sim_path("m"))?;
    let mut summary = String::from(
        "| ELF | function | address | bytes | L0 | L1 | L2 | L3 | L4 | native = P-mem G/M | layers agree |\n|---|---|---|---:|---:|---:|---:|---:|---:|---|---|\n",
    );
    let mut bad = 0;
    for e in &t.elfs {
        let elf = Elf::parse(std::fs::read(base.join(&e.path)).with_context(|| e.path.clone())?)?;
        let spec_text = match &e.spec {
            Some(s) => Some(std::fs::read_to_string(base.join(s))?),
            None => None,
        };
        for f in &e.functions {
            if !a.only.is_empty() && !a.only.contains(&f.name) {
                continue;
            }
            let c = cut(&elf, &f.name)?;
            let kinds: Vec<K> = f.args.iter().map(|s| parse_arg(s)).collect::<Result<_>>()?;
            let uses_mem = kinds.iter().any(|k| !matches!(k, K::V(_)));
            let dir = a.out.join(&e.name).join(&f.name);
            std::fs::create_dir_all(&dir)?;
            println!(
                "== {}:{} at {:#x}, {} bytes: {}",
                e.name,
                f.name,
                c.addr,
                c.size,
                hex(c.bytes())
            );
            std::fs::write(
                dir.join("bytes.txt"),
                format!("{} {:#x} {} {}\n", e.path, c.addr, c.size, hex(c.bytes())),
            )?;

            // ---- layers
            let mut wats: Vec<Option<String>> = vec![None; 5];
            wats[0] = Some(layer0(&f.name, &c)?);
            wats[1] = Some(layer1(&f.name, &c)?);
            for (k, w) in wats.iter().enumerate().take(2) {
                std::fs::write(dir.join(format!("L{k}.wat")), w.as_ref().unwrap())?;
            }
            if !a.no_opt {
                let l1w = dir.join("L1.wasm");
                std::fs::write(&l1w, wat::parse_str(wats[1].as_ref().unwrap())?)?;
                let inl = dir.join("L1-inlined.wat");
                inline_all(&l1w, &inl)?;
                let l2 = localize(&std::fs::read_to_string(&inl)?)?;
                // binaryen's printer is not always standard WAT (unreachable code): go through
                // binary and print with wasm2wat
                let raw = dir.join("L2-raw.wat");
                std::fs::write(&raw, &l2)?;
                let l2w = dir.join("L2.wasm");
                let l3w = dir.join("L3.wasm");
                run_tool(
                    Command::new("wasm-opt")
                        .arg(&raw)
                        .args(["-g", "--enable-bulk-memory", "--enable-sign-ext", "-o"])
                        .arg(&l2w),
                )?;
                run_tool(
                    Command::new("wasm-opt")
                        .arg(&l2w)
                        .args([
                            "-g",
                            "--enable-bulk-memory",
                            "--enable-sign-ext",
                            "-O3",
                            "-o",
                        ])
                        .arg(&l3w),
                )?;
                for (k, w) in [(2usize, &l2w), (3, &l3w)] {
                    let out = dir.join(format!("L{k}.wat"));
                    run_tool(Command::new("wasm2wat").arg(w).arg("-o").arg(&out))?;
                    wats[k] = Some(std::fs::read_to_string(&out)?);
                }
                for x in [&l1w, &l2w, &l3w, &inl, &raw] {
                    let _ = std::fs::remove_file(x);
                }
            }
            if let (Some(st), Some(sig)) = (&spec_text, &f.sig) {
                let l4 = format!(
                    ";; L4 (spec) for `{}`: hand-written Wasm over C types (examples/wasm-sim/elf-verify), plus the ABI adapter.\n(module\n{st}{})\n",
                    f.name,
                    adapter(&f.name, sig, st.contains("(memory"))?
                );
                std::fs::write(dir.join("L4.wat"), &l4)?;
                wats[4] = Some(l4);
            }
            let mods: Vec<Option<Module>> = wats
                .iter()
                .enumerate()
                .map(|(k, w)| {
                    w.as_ref()
                        .map(|w| {
                            Module::new(&engine, w).map_err(|e| anyhow!("{} L{k}: {e:?}", f.name))
                        })
                        .transpose()
                })
                .collect::<Result<_>>()?;

            // ---- native vs P-mem (full state) and vs every layer (rax, ABI)
            let mut nat = Native::new();
            let fbase = nat.place_code(&c.text);
            let target = fbase + (c.addr - c.text_addr);
            let mut call = vec![0xe8u8];
            call.extend_from_slice(&((target as i64 - nat.fall as i64) as i32).to_le_bytes());
            let at = nat.place(&call);
            let data = super::native::mmap(difftest::DATA_LEN, false);
            // SAFETY: fresh mapping used only here.
            let dbuf: &mut [u8] =
                unsafe { std::slice::from_raw_parts_mut(data, difftest::DATA_LEN) };
            let dbase = data as u64;
            let mut sims_g = difftest::sims_for(
                &engine,
                &sim_g,
                vec![nat.range(), (dbase, dbase + difftest::DATA_LEN as u64)],
            )?;
            let mut sims_m = difftest::sims_for(
                &engine,
                &sim_m,
                vec![nat.range(), (dbase, dbase + difftest::DATA_LEN as u64)],
            )?;
            let mut rng = Rng(a.seed ^ c.addr);
            let (mut pmem_fail, mut layer_fail) = (0, 0);
            for _ in 0..a.per {
                let mut st = State::default();
                for r in st.r.iter_mut() {
                    *r = rng.val();
                }
                st.r[4] = dbase + difftest::RSP_OFF;
                st.flags = rng.next_u64() & 0x8d5;
                let mut area: Vec<u8> = (0..ABUF).map(|_| rng.next_u64() as u8).collect();
                let (args, wa) = gen_args(&mut rng, &kinds, dbase, &mut area);
                for (r, v) in [7usize, 6, 2, 1, 8, 9].iter().zip(&args) {
                    st.r[*r] = *v;
                }
                let mut full = vec![0u8; difftest::DATA_LEN];
                full[NBUF..NBUF + ABUF].copy_from_slice(&area);
                dbuf.copy_from_slice(&full);
                // SAFETY: the functions only touch the buffer area (arguments) and the stack,
                // both in the data buffer.
                let ns = unsafe { nat.run(&st) };
                let no = difftest::obs_native(&ns, dbuf);
                let narea = dbuf[NBUF..NBUF + ABUF].to_vec();
                let mut d = String::new();
                for sims in [&mut sims_g, &mut sims_m] {
                    dbuf.copy_from_slice(&full);
                    let o0 =
                        difftest::obs_sim(&mut sims[0], &st, at, &[nat.fall], 10_000_000, dbuf);
                    dbuf.copy_from_slice(&full);
                    let o1 =
                        difftest::obs_sim(&mut sims[1], &st, at, &[nat.fall], 10_000_000, dbuf);
                    d += &difftest::compare(&no, &o0, &o1);
                }
                if !d.is_empty() {
                    pmem_fail += 1;
                    if pmem_fail <= 3 {
                        println!("  P-mem FAIL {args:x?}: {d}");
                    }
                }
                // the layers: wrapper arguments from the same entry state, pointers moved to
                // the guest buffer; a native pointer result is compared after the same move
                let mut gst = st;
                for (r, v) in [7usize, 6, 2, 1, 8, 9].iter().zip(&wa) {
                    gst.r[*r] = *v;
                }
                let wargs: Vec<u64> = PREGS
                    .iter()
                    .map(|&l| gst.r[l as usize])
                    .chain([0u32, 2, 4, 6, 7, 11].iter().map(|b| (st.flags >> b) & 1))
                    .collect();
                let nb = dbase + NBUF as u64;
                let want = if uses_mem && ns.r[0] >= nb && ns.r[0] <= nb + ABUF as u64 {
                    ns.r[0] - nb + WBUF
                } else {
                    ns.r[0]
                };
                for (k, m) in mods.iter().enumerate() {
                    let Some(m) = m else { continue };
                    let (r0, a0) = call_layer(&engine, m, Undef::Zero, &wargs, &area)?;
                    let (r1, a1) = call_layer(&engine, m, Undef::Ones, &wargs, &area)?;
                    let mem_ok = !uses_mem || (a0 == narea && a1 == narea);
                    if r0 != Some(want) || r1 != Some(want) || !mem_ok {
                        layer_fail += 1;
                        if layer_fail <= 3 {
                            println!(
                                "  L{k} FAIL {args:x?}: native rax {want:#x}, layer {r0:x?}/{r1:x?}, memory {}",
                                if mem_ok { "ok" } else { "DIFFERS" }
                            );
                        }
                    }
                }
            }
            println!(
                "  native vs P-mem G,M (all GPRs, rip, flags, stack): {} runs, {pmem_fail} failures",
                a.per
            );
            println!(
                "  native rax vs layers {}: {} runs, {layer_fail} failures",
                (0..5)
                    .filter(|k| mods[*k].is_some())
                    .map(|k| LAYERS[k])
                    .collect::<Vec<_>>()
                    .join(","),
                a.per
            );
            bad += pmem_fail + layer_fail;

            // ---- solver problems: adjacent layers, and the contract on L4 and on L1
            let unroll = f.unroll.unwrap_or(8);
            let regmap: Vec<(String, String)> = super::NAMES[..23]
                .iter()
                .filter(|n| **n != "pf" && **n != "af")
                .map(|n| (format!("g:{n}"), format!("g:{n}")))
                .collect();
            let _ = regmap;
            let pre = contract_to_params(&f.requires);
            let pre_defs: Vec<String> = t
                .defs
                .iter()
                .filter(|(dn, _)| f.requires.contains(dn.as_str()))
                .map(|(_, d)| format!("\"{}\"", d.replace('"', "\\\"")))
                .collect();
            let pairs: Vec<(usize, usize, Vec<&str>)> = vec![
                (1, 2, vec!["result", "trap", "memory"]),
                (2, 3, vec!["result", "trap", "memory"]),
                (
                    3,
                    4,
                    if uses_mem {
                        vec!["result", "trap", "memory"]
                    } else {
                        vec!["result", "trap"]
                    },
                ),
            ];
            {
                let (i0, i1, probs) = insn_tv(&f.name, &c)?;
                let d = dir.join("tv-01");
                std::fs::create_dir_all(&d)?;
                std::fs::write(d.join("I0.wat"), i0)?;
                std::fs::write(d.join("I1.wat"), i1)?;
                for (a, t) in probs {
                    std::fs::write(d.join(format!("insn-{a:x}.toml")), t)?;
                }
            }
            for (x, y, obs) in pairs {
                if mods[x].is_none() || mods[y].is_none() {
                    continue;
                }
                let n = format!("{}-tv-{x}{y}", f.name);
                std::fs::write(
                    dir.join(format!("tv-{x}{y}.toml")),
                    tv_problem(
                        &n,
                        &f.name,
                        LAYERS[x],
                        LAYERS[y],
                        &obs,
                        &[],
                        &(if x == 3 {
                            contract_to_pidx(&f.requires)
                        } else {
                            pre.clone()
                        }),
                        unroll,
                        if uses_mem { "symbolic" } else { "module" },
                        &pre_defs,
                    ),
                )?;
            }
            for k in [1usize, 4] {
                if mods[k].is_none() {
                    continue;
                }
                let mut p = format!(
                    "# The C-level contract of `{}` on layer L{k} (GENERATED by `wasm-sim elfv`).\nname = \"{}-post-L{k}\"\nkind = \"post\"\ninit = \"{}\"\nunroll = {unroll}\nno_trap = true\nmodules = [{{ name = \"m\", wat = \"L{k}.wat\" }}]\nentry = \"f\"\n",
                    f.name,
                    f.name,
                    if uses_mem { "symbolic" } else { "module" }
                );
                if pre != "true" {
                    let _ = writeln!(p, "pre = [\"{}\"]", pre.replace('"', "\\\""));
                }
                let mut defines = vec![];
                for (dn, d) in &t.defs {
                    if f.ensures.contains(dn.as_str()) || f.requires.contains(dn.as_str()) {
                        defines.push(format!("\"{}\"", d.replace('"', "\\\"")));
                    }
                }
                if !defines.is_empty() {
                    let _ = writeln!(p, "defines = [{}]", defines.join(", "));
                }
                let _ = writeln!(
                    p,
                    "post = [\"{}\"]",
                    contract_to_params(&f.ensures).replace('"', "\\\"")
                );
                std::fs::write(dir.join(format!("post-L{k}.toml")), p)?;
            }
            let sizes: Vec<String> = (0..5)
                .map(|k| {
                    wats[k]
                        .as_ref()
                        .map(|w| count_instrs(w).to_string())
                        .unwrap_or("-".into())
                })
                .collect();
            let _ = writeln!(
                summary,
                "| {} | {} | {:#x} | {} | {} | {} | {} | {} | {} | {} | {} |",
                e.name,
                f.name,
                c.addr,
                c.size,
                sizes[0],
                sizes[1],
                sizes[2],
                sizes[3],
                sizes[4],
                if pmem_fail == 0 {
                    format!("{} ok", a.per)
                } else {
                    format!("{pmem_fail} FAIL")
                },
                if layer_fail == 0 {
                    format!("{} ok", a.per)
                } else {
                    format!("{layer_fail} FAIL")
                }
            );
        }
    }
    std::fs::write(a.out.join("summary.md"), &summary)?;
    print!("{summary}");
    if bad > 0 {
        bail!("{bad} failures");
    }
    Ok(())
}
