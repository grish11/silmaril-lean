//! x86 functions + System V contracts  ->  Wasm problems.
//!
//! Input: `tests/contracts.toml` (schema `silmaril.wasm-sim.contracts.v0`, vocabulary of the
//! reduction plans: `(reg r)` = location after the call, `(old t)` = `t` at entry,
//! `(mem8 a)`/`(mem16 a)`/`(mem32 a)`/`(mem64 a)` = little-endian bytes at guest address `a`).
//!
//! Output (`wasm-sim problems -o DIR`):
//! * `closed/<f>.wat`: one closed module per contract: G methods (pruned), memory window as an
//!   imported memory (`src/mem-window.wat`), the P-calls translation of `f` and its callees, and
//!   a wrapper `f(rax..r15, cf pf af zf sf of df)` that loads *every* GPR and flag from its
//!   parameters, runs `f` and traps unless the System V return obligations (rip = the return
//!   address read from [rsp] at entry, rsp + 8, rbx rbp r12-r15 restored) and the frame (no byte
//!   of the window outside the footprint changed) hold. Annotated `@requires` (ABI entry
//!   alignment + window + contract) and `@ensures` (contract); see
//!   `examples/wasm-sim/x86/problems/README.md` for the correspondence with
//!   `FnContract.Spec.Total`.
//! * `split/`: the decomposition: `sim.wat` (the simulator, one shared instance), one module per
//!   x86 function importing the simulator's methods and its callees (`<callee>.<callee>`),
//!   annotated `@requires/@ensures/@assume`; `pieces/<f>.json` (schema
//!   `silmaril.wasm-sim.piece.v0`) and `link.json` (instantiation order). Composition = linking.
//!
//! `--check`: runs every closed problem and the linked split modules from random states and
//! compares with the P-mem simulator (registers, flags, window), and asks z3 whether
//! `requires => ensures` holds on each concrete (entry, exit) pair.

use super::difftest::{self, Arg, CODE_BASE, DATA_BASE, Rng, Suite};
use super::pcalls::{self, Func, Opts, decode_all, translate_func};
use super::sexp::{self, Sexp};
use super::{NAMES, RIP};
use crate::harness::{self, Host, PageMem, Sim, Undef};
use anyhow::{Context, Result, anyhow, bail};
use serde::Deserialize;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use wasmtime::{Engine, Linker, Memory, MemoryType, Module, Store, Val};

pub const WINDOW: u64 = DATA_BASE; // 0x100000
pub const WINDOW_LEN: u64 = 0x10000;
/// Stack frame part of every footprint: [rsp - STACK_FRAME, rsp).
pub const STACK_FRAME: u64 = 0x1000;
pub const FLAGS: [&str; 7] = ["cf", "pf", "af", "zf", "sf", "of", "df"];
pub const CALLEE_SAVED: [i32; 6] = [3, 5, 12, 13, 14, 15];

#[derive(Deserialize, Clone, Debug)]
pub struct Contract {
    pub name: String,
    /// "funcs.S" or "cfuncs.c" (in tests/)
    pub source: String,
    pub requires: String,
    pub ensures: String,
    /// extra write ranges [lo, hi) as terms over `(old (reg r))`
    #[serde(default)]
    pub footprint: Vec<[String; 2]>,
    /// stack frame size (bytes below rsp the function may write; default 0x1000). A callee
    /// must have a smaller frame than its caller minus the caller's own pushes, so that its
    /// entry obligations (rsp >= window + frame) and its frame follow from the caller's.
    #[serde(default = "default_frame")]
    pub frame: u64,
}

fn default_frame() -> u64 {
    STACK_FRAME
}

#[derive(Deserialize, Debug)]
pub struct Contracts {
    pub schema: String,
    #[serde(default)]
    pub defs: BTreeMap<String, String>,
    pub function: Vec<Contract>,
}

pub fn read_contracts(p: &Path) -> Result<Contracts> {
    let c: Contracts = toml::from_str(&std::fs::read_to_string(p)?)?;
    if c.schema != "silmaril.wasm-sim.contracts.v0" {
        bail!("unknown schema {}", c.schema);
    }
    Ok(c)
}

/// The implicit entry obligations: AbiEntry alignment, stack frame and [rsp] inside the window.
pub fn abi_requires(frame: u64) -> String {
    format!(
        "(and (= ((_ extract 3 0) (old (reg rsp))) #x8) (bvuge (old (reg rsp)) #x{:016x}) (bvule (old (reg rsp)) #x{:016x}))",
        WINDOW + frame,
        WINDOW + WINDOW_LEN - 8
    )
}

fn full_requires(c: &Contract) -> String {
    format!("(and {} {})", abi_requires(c.frame), c.requires)
}

// ------------------------------------------------------------------ term translations

/// Footprint term -> WAT i64 expression over the wrapper's parameters.
fn term_wat(t: &Sexp) -> Result<String> {
    Ok(match t {
        Sexp::Atom(a) if a.starts_with("#x") => format!("(i64.const 0x{})", &a[2..]),
        Sexp::Atom(a) => bail!("footprint atom {a}"),
        _ => match t.head() {
            Some("old") => match &t.args()[0] {
                r if r.head() == Some("reg") => format!("(local.get ${})", r.args()[0]),
                x => bail!("footprint: (old {x})"),
            },
            Some(op @ ("bvadd" | "bvsub" | "bvmul")) => {
                let o = &op[2..];
                format!(
                    "(i64.{o} {} {})",
                    term_wat(&t.args()[0])?,
                    term_wat(&t.args()[1])?
                )
            }
            Some("_") => format!(
                "(i64.const {})",
                t.args()[0].to_string().trim_start_matches("bv")
            ),
            _ => bail!("footprint term {t}"),
        },
    })
}

/// Contract term -> SMT-LIB over constants old_r / new_r and functions old_memN / new_memN.
pub fn term_smt(s: &str) -> Result<String> {
    Ok(smt_of(&sexp::parse(s)?).to_string())
}

fn smt_of(e: &Sexp) -> Sexp {
    let at = |s: String| Sexp::Atom(s);
    let mem = |h: Option<&str>| matches!(h, Some("mem8" | "mem16" | "mem32" | "mem64"));
    match e.head() {
        Some("old") => {
            let x = &e.args()[0];
            match x.head() {
                Some("reg") => at(format!("old_{}", x.args()[0])),
                h if mem(h) => Sexp::List(vec![
                    at(format!("old_{}", h.unwrap())),
                    smt_of(&x.args()[0]),
                ]),
                _ => smt_of(x),
            }
        }
        Some("reg") => at(format!("new_{}", e.args()[0])),
        h if mem(h) => Sexp::List(vec![
            at(format!("new_{}", h.unwrap())),
            smt_of(&e.args()[0]),
        ]),
        _ => match e {
            Sexp::List(v) => Sexp::List(v.iter().map(smt_of).collect()),
            a => a.clone(),
        },
    }
}

// ------------------------------------------------------------------ closed problems

fn suite_for(c: &Contract) -> Result<Suite> {
    difftest::suite(c.source.ends_with(".c"))
}

fn kinds_for(c: &Contract) -> Result<&'static [Arg]> {
    difftest::FUNCS
        .iter()
        .chain(difftest::CFUNCS)
        .find(|f| f.0 == c.name)
        .map(|f| f.1)
        .with_context(|| format!("no argument kinds for {}", c.name))
}

fn defs_comment(defs: &BTreeMap<String, String>) -> String {
    defs.values().map(|d| format!(";; @define {d}\n")).collect()
}

/// The closed wrapper: all locations from parameters, run, check AbiReturn and frame.
fn wrapper(c: &Contract, entry: u64) -> Result<String> {
    let mut w = String::new();
    let params: String = NAMES[..16]
        .iter()
        .chain(FLAGS.iter())
        .map(|n| format!(" (param ${n} i64)"))
        .collect();
    writeln!(
        w,
        "  ;; System V wrapper for `{}` at {entry:#x}: all GPRs and flags are parameters (= (old (reg r))).",
        c.name
    )?;
    writeln!(
        w,
        "  ;; Traps unless AbiReturn (rip = [rsp]@entry, rsp+8, rbx rbp r12-r15 kept) and the frame hold."
    )?;
    writeln!(w, "  ;; @requires {}", full_requires(c))?;
    writeln!(w, "  ;; @ensures {}", c.ensures)?;
    let mut fp = vec![format!(
        "[(bvsub (old (reg rsp)) #x{:016x}), (old (reg rsp)))",
        c.frame
    )];
    fp.extend(c.footprint.iter().map(|[l, h]| format!("[{l}, {h})")));
    writeln!(w, "  ;; @footprint {}", fp.join(" "))?;
    writeln!(
        w,
        "  (func ${n} (export \"{n}\"){params}\n    (local $ret i64) (local $i i32) (local $a i64)",
        n = c.name
    )?;
    for (l, n) in NAMES[..16].iter().enumerate() {
        writeln!(w, "    (call $set (i32.const {l}) (local.get ${n}))")?;
    }
    for (k, n) in FLAGS.iter().enumerate() {
        writeln!(w, "    (call $set (i32.const {}) (local.get ${n}))", 17 + k)?;
    }
    writeln!(w, "    (local.set $ret (call $load64 (local.get $rsp)))")?;
    writeln!(
        w,
        "    (memory.copy (i32.const 0x10000) (i32.const 0) (i32.const 0x10000))"
    )?;
    writeln!(w, "    (call $set (i32.const 16) (i64.const {entry}))")?;
    writeln!(
        w,
        "    (if (i32.ne (call $f_{entry:x}) (i32.const 0)) (then (unreachable)))"
    )?;
    writeln!(
        w,
        "    (if (i64.ne (call $get (i32.const 16)) (local.get $ret)) (then (unreachable)))"
    )?;
    writeln!(
        w,
        "    (if (i64.ne (call $get (i32.const 4)) (i64.add (local.get $rsp) (i64.const 8))) (then (unreachable)))"
    )?;
    for r in CALLEE_SAVED {
        writeln!(
            w,
            "    (if (i64.ne (call $get (i32.const {r})) (local.get ${})) (then (unreachable)))",
            NAMES[r as usize]
        )?;
    }
    // frame check
    let mut infp = format!(
        "(i32.and (i64.ge_u (local.get $a) (i64.sub (local.get $rsp) (i64.const {}))) (i64.lt_u (local.get $a) (local.get $rsp)))",
        c.frame
    );
    for [l, h] in &c.footprint {
        let (l, h) = (term_wat(&sexp::parse(l)?)?, term_wat(&sexp::parse(h)?)?);
        infp = format!(
            "(i32.or {infp}\n          (i32.and (i64.ge_u (local.get $a) {l}) (i64.lt_u (local.get $a) {h})))"
        );
    }
    writeln!(
        w,
        "    (loop $frame\n      (local.set $a (i64.add (i64.const {WINDOW}) (i64.extend_i32_u (local.get $i))))\n      (if (i32.eqz {infp})\n        (then (if (i32.ne (i32.load8_u (local.get $i)) (i32.load8_u offset=0x10000 (local.get $i))) (then (unreachable)))))\n      (local.set $i (i32.add (local.get $i) (i32.const 1)))\n      (br_if $frame (i32.lt_u (local.get $i) (i32.const 0x10000)))))"
    )?;
    Ok(w)
}

pub fn closed_module(
    c: &Contract,
    defs: &BTreeMap<String, String>,
    code: &[u8],
    entry: u64,
) -> Result<String> {
    let funcs = decode_all(code, CODE_BASE, &[entry])?;
    let mut used = BTreeSet::new();
    let mut body = String::new();
    for f in &funcs {
        body += &translate_func(f, &Opts::default(), &mut used)?;
    }
    let text = format!(
        ";; Wasm problem for the x86-64 function `{n}` (GENERATED by `wasm-sim problems`; see
;; docs/wasm-sim-abi.md and examples/wasm-sim/x86/problems/README.md for the correspondence with
;; FnContract.Spec.Total on Open9). Simulator: G state + methods (src/core.wat); memory: the
;; imported window env.mem (src/mem-window.wat); nd.undef and sys.syscall are imports.
;; Vocabulary: (old (reg r)) = parameter r; (reg r) = location r after the call (export get);
;; (memN a) = little-endian bytes of the window at guest address a after, (old (memN a)) before.
{}{}{}{}{}  ;; ---- program (P-calls translation of the machine code)
{body}{}{})\n",
        super::src("header.wat")?,
        super::src("mem-window.wat")?,
        super::src("state-g.wat")?,
        super::src("core.wat")?,
        "",
        defs_comment(defs),
        wrapper(c, entry)?,
        n = c.name,
    );
    Ok(super::prune::prune(
        &text,
        &[&format!("${}", c.name), "$get"],
    ))
}

// ------------------------------------------------------------------ split problems

/// A split module: (name, address, module text, imports-from-sim, callee names).
pub type SplitModule = (String, u64, String, Vec<String>, Vec<String>);

pub struct Split {
    pub sim: String,
    /// (name, address, module text, imports-from-sim, callee names)
    pub modules: Vec<SplitModule>,
    /// instantiation order (callees first)
    pub order: Vec<String>,
}

fn fname(addr: u64, names: &BTreeMap<u64, String>) -> String {
    names
        .get(&addr)
        .cloned()
        .unwrap_or_else(|| format!("f_{addr:x}"))
}

/// The shared simulator module for split problems (G, mem.* imports, no decoder).
pub fn split_sim() -> Result<String> {
    Ok(format!(
        ";; Shared simulator for split problems: G state + methods; memory through mem.* imports.\n{}{}{}{})\n",
        super::src("header.wat")?,
        super::src("mem-import.wat")?,
        super::src("state-g.wat")?,
        super::src("core.wat")?
    ))
}

pub fn split(
    root: u64,
    code: &[u8],
    syms: &BTreeMap<String, u64>,
    contracts: &BTreeMap<String, &Contract>,
    defs: &BTreeMap<String, String>,
    sim_m: &Module,
) -> Result<Split> {
    let names: BTreeMap<u64, String> = syms
        .iter()
        .map(|(n, a)| (CODE_BASE + a, n.clone()))
        .collect();
    let funcs: Vec<Func> = decode_all(code, CODE_BASE, &[root])?;
    let by_addr: BTreeMap<u64, &Func> = funcs.iter().map(|f| (f.entry, f)).collect();
    // callee-first order (DFS post-order); mutual recursion is rejected
    let mut order = vec![];
    let mut state: BTreeMap<u64, u8> = BTreeMap::new();
    fn visit(
        a: u64,
        by: &BTreeMap<u64, &Func>,
        st: &mut BTreeMap<u64, u8>,
        out: &mut Vec<u64>,
    ) -> Result<()> {
        match st.get(&a) {
            Some(2) => return Ok(()),
            Some(1) => bail!(
                "mutual recursion through {a:#x}: split needs an acyclic call graph (self-calls are fine)"
            ),
            _ => {}
        }
        st.insert(a, 1);
        for &c in &by[&a].callees {
            if c != a {
                visit(c, by, st, out)?;
            }
        }
        st.insert(a, 2);
        out.push(a);
        Ok(())
    }
    visit(root, &by_addr, &mut state, &mut order)?;
    let mut modules = vec![];
    for &a in &order {
        let f = by_addr[&a];
        let name = fname(a, &names);
        let mut used = BTreeSet::new();
        let body = translate_func(f, &Opts::default(), &mut used)?;
        let mut w = String::new();
        writeln!(
            w,
            ";; x86-64 function `{name}` at {a:#x} as one piece of a split problem (GENERATED by `wasm-sim problems`)."
        )?;
        writeln!(
            w,
            ";; Imports the shared simulator `sim` (its state is the machine state) and its callees."
        )?;
        writeln!(
            w,
            ";; Vocabulary: (reg r) after, (old t) at entry of this function; AbiEntry assumed,"
        )?;
        writeln!(
            w,
            ";; AbiReturn and the frame are part of every contract (implicit, as in FnContract.Spec)."
        )?;
        w += &defs_comment(defs);
        writeln!(w, "(module")?;
        let mut sim_imports = vec![];
        for n in &used {
            let wasmtime::ExternType::Func(ft) = sim_m
                .get_export(n)
                .with_context(|| format!("sim lacks {n}"))?
            else {
                bail!("{n}")
            };
            let ps: Vec<String> = ft.params().map(|t| format!("{t}")).collect();
            let rs: Vec<String> = ft.results().map(|t| format!("{t}")).collect();
            let sig = format!(
                "{}{}",
                if ps.is_empty() {
                    String::new()
                } else {
                    format!(" (param {})", ps.join(" "))
                },
                if rs.is_empty() {
                    String::new()
                } else {
                    format!(" (result {})", rs.join(" "))
                }
            );
            writeln!(w, "  (import \"sim\" \"{n}\" (func ${n}{sig}))")?;
            sim_imports.push(n.to_string());
        }
        let mut callees = vec![];
        for &c in &f.callees {
            if c == a {
                continue;
            }
            let cn = fname(c, &names);
            match contracts.get(&cn) {
                Some(k) => writeln!(
                    w,
                    "  ;; @assume {cn} (=> {} {})",
                    full_requires(k),
                    k.ensures
                )?,
                None => writeln!(
                    w,
                    "  ;; @assume {cn} true  (no contract: only the System V obligations)"
                )?,
            }
            writeln!(
                w,
                "  (import \"{cn}\" \"{cn}\" (func $f_{c:x} (result i32)))"
            )?;
            callees.push(cn);
        }
        if let Some(k) = contracts.get(&name) {
            writeln!(w, "  ;; @requires {}", full_requires(k))?;
            writeln!(w, "  ;; @ensures {}", k.ensures)?;
        }
        w += &body;
        writeln!(w, "  (export \"{name}\" (func $f_{a:x})))")?;
        modules.push((name.clone(), a, w, sim_imports, callees));
    }
    Ok(Split {
        sim: split_sim()?,
        order: order.iter().map(|a| fname(*a, &names)).collect(),
        modules,
    })
}

pub fn piece_json(
    name: &str,
    addr: u64,
    bytes: &[u8],
    sim: &[String],
    callees: &[String],
    k: Option<&Contract>,
    contracts: &BTreeMap<String, &Contract>,
) -> serde_json::Value {
    let hex: String = bytes.iter().map(|b| format!("{b:02x}")).collect();
    serde_json::json!({
        "schema": "silmaril.wasm-sim.piece.v0",
        "id": format!("wasm-sim/x86/{name}/ag"),
        "kind": "assume-guarantee",
        "function": name,
        "address": format!("{addr:#x}"),
        "bytes": hex,
        "program": { "kind": "annotated-wat", "source": format!("../{name}.wat"),
                     "imports": { "sim": sim, "callees": callees } },
        "spec": {
            "requires": k.map(full_requires).unwrap_or_else(|| abi_requires(STACK_FRAME)),
            "ensures": k.map(|k| k.ensures.clone()).unwrap_or_else(|| "true".into()),
            "assumes": callees.iter().map(|c| serde_json::json!({
                "import": c,
                "requires": contracts.get(c).map(|k| full_requires(k)).unwrap_or_else(|| abi_requires(STACK_FRAME)),
                "ensures": contracts.get(c).map(|k| k.ensures.clone()).unwrap_or_else(|| "true".into())})).collect::<Vec<_>>(),
            "abi": "AbiEntry assumed; AbiReturn (rip, rsp+8, rbx rbp r12-r15) and frame (footprint + [rsp-0x1000, rsp)) required"
        },
        "statement": format!("assuming the callees {callees:?} meet their contracts (imports), `{name}` (module linked to the shared simulator) meets its contract"),
        "status": "open",
        "solvers": ["wpc/HWP", "wasm-vc (tools/wasm-vc sym)", "agent"]
    })
}

// ------------------------------------------------------------------ CLI

#[derive(clap::Args)]
pub struct Args {
    /// contracts (default examples/wasm-sim/x86/tests/contracts.toml)
    #[arg(long)]
    contracts: Option<PathBuf>,
    /// only these functions
    #[arg(long, value_delimiter = ',')]
    only: Vec<String>,
    /// output directory (default examples/wasm-sim/x86/problems)
    #[arg(long, short)]
    out: Option<PathBuf>,
    /// check the emitted problems (random states vs P-mem, z3 on concrete pairs)
    #[arg(long)]
    check: bool,
    #[arg(long, default_value_t = 50)]
    per: usize,
    #[arg(long, default_value_t = 1)]
    seed: u64,
}

pub fn main(a: Args) -> Result<()> {
    let cpath = a
        .contracts
        .clone()
        .unwrap_or_else(|| super::x86_dir().join("tests/contracts.toml"));
    let cs = read_contracts(&cpath)?;
    let out = a
        .out
        .clone()
        .unwrap_or_else(|| super::x86_dir().join("problems"));
    let engine = harness::engine();
    let sim_text = split_sim()?;
    let sim_m = Module::new(&engine, &sim_text).map_err(|e| anyhow!("{e:?}"))?;
    let all: BTreeMap<String, &Contract> =
        cs.function.iter().map(|c| (c.name.clone(), c)).collect();
    std::fs::create_dir_all(out.join("closed"))?;
    std::fs::create_dir_all(out.join("split"))?;
    std::fs::write(out.join("split/sim.wat"), &sim_text)?;
    let mut bad = 0;
    for c in &cs.function {
        if !a.only.is_empty() && !a.only.contains(&c.name) {
            continue;
        }
        let suite = suite_for(c)?;
        let entry = CODE_BASE
            + *suite
                .syms
                .get(&c.name)
                .with_context(|| format!("no symbol {}", c.name))?;
        let closed = closed_module(c, &cs.defs, &suite.code, entry)?;
        std::fs::write(out.join(format!("closed/{}.wat", c.name)), &closed)?;
        // split: one directory per root function
        let sp = split(entry, &suite.code, &suite.syms, &all, &cs.defs, &sim_m)?;
        let dir = out.join("split").join(&c.name);
        std::fs::create_dir_all(dir.join("pieces"))?;
        let funcs = decode_all(&suite.code, CODE_BASE, &[entry])?;
        for (n, addr, text, sim, callees) in &sp.modules {
            std::fs::write(dir.join(format!("{n}.wat")), text)?;
            let f = funcs.iter().find(|f| f.entry == *addr).unwrap();
            let lo = (f.entry - CODE_BASE) as usize;
            let hi = f
                .insns
                .iter()
                .next_back()
                .map(|(a, i)| (a - CODE_BASE) as usize + i.len())
                .unwrap_or(lo);
            let pj = piece_json(
                n,
                *addr,
                &suite.code[lo..hi],
                sim,
                callees,
                all.get(n).copied(),
                &all,
            );
            std::fs::write(
                dir.join(format!("pieces/{n}.json")),
                serde_json::to_string_pretty(&pj)?,
            )?;
        }
        std::fs::write(
            dir.join("link.json"),
            serde_json::to_string_pretty(&serde_json::json!({
                "schema": "silmaril.wasm-sim.link.v0", "sim": "../sim.wat", "order": sp.order, "root": c.name,
                "env": ["mem.load8..64/store8..64", "sys.syscall", "nd.undef"]}))?,
        )?;
        if a.check {
            match check(
                &engine, c, &cs.defs, &suite, entry, &closed, &sp, &sim_m, a.per, a.seed,
            ) {
                Ok(msg) => println!("{:<10} {msg}", c.name),
                Err(e) => {
                    bad += 1;
                    println!("{:<10} FAIL {e:#}", c.name);
                }
            }
        } else {
            println!(
                "{:<10} closed {} lines, split {} modules",
                c.name,
                closed.lines().count(),
                sp.modules.len()
            );
        }
    }
    if bad > 0 {
        bail!("{bad} problems failed");
    }
    Ok(())
}

// ------------------------------------------------------------------ checks

struct Outcome {
    regs: Vec<u64>, // 0..15, then flags 17..22
    window: Vec<u8>,
}

fn smt_bytes(name: &str, base: u64, bytes: &[u8], ranges: &[(u64, u64)]) -> String {
    let mut s = format!("(declare-const {name}_m (Array (_ BitVec 64) (_ BitVec 8)))\n");
    for &(lo, hi) in ranges {
        for a in lo.max(base)..hi.min(base + bytes.len() as u64) {
            writeln!(
                s,
                "(assert (= (select {name}_m #x{a:016x}) #x{:02x}))",
                bytes[(a - base) as usize]
            )
            .unwrap();
        }
    }
    writeln!(
        s,
        "(define-fun {name}_mem8 ((a (_ BitVec 64))) (_ BitVec 8) (select {name}_m a))"
    )
    .unwrap();
    writeln!(s, "(define-fun {name}_mem16 ((a (_ BitVec 64))) (_ BitVec 16) (concat ({name}_mem8 (bvadd a #x0000000000000001)) ({name}_mem8 a)))").unwrap();
    writeln!(s, "(define-fun {name}_mem32 ((a (_ BitVec 64))) (_ BitVec 32) (concat ({name}_mem16 (bvadd a #x0000000000000002)) ({name}_mem16 a)))").unwrap();
    writeln!(s, "(define-fun {name}_mem64 ((a (_ BitVec 64))) (_ BitVec 64) (concat ({name}_mem32 (bvadd a #x0000000000000004)) ({name}_mem32 a)))").unwrap();
    s
}

#[allow(clippy::too_many_arguments)]
fn check(
    engine: &Engine,
    c: &Contract,
    defs: &BTreeMap<String, String>,
    suite: &Suite,
    entry: u64,
    closed: &str,
    sp: &Split,
    sim_m: &Module,
    per: usize,
    seed: u64,
) -> Result<String> {
    let kinds = kinds_for(c)?;
    let closed_m = Module::new(engine, closed).map_err(|e| anyhow!("closed module: {e:?}"))?;
    let split_ms: Vec<(String, Module)> = sp
        .modules
        .iter()
        .map(|(n, _, t, _, _)| {
            Ok((
                n.clone(),
                Module::new(engine, t).map_err(|e| anyhow!("split {n}: {e:?}"))?,
            ))
        })
        .collect::<Result<_>>()?;
    let mut rng = Rng(seed ^ 0xc0ffee);
    let mut smt = String::from("(set-option :produce-models false)\n");
    let (req, ens) = (term_smt(&full_requires(c))?, term_smt(&c.ensures)?);
    let mut z3_cases = 0;
    for _ in 0..per {
        // entry state: random GPRs and flags, arguments, rsp in the window, random window bytes
        let mut fill: Vec<u8> = (0..WINDOW_LEN).map(|_| rng.next_u64() as u8).collect();
        let args = difftest::gen_args(&mut rng, kinds, WINDOW, &mut fill);
        let mut regs: Vec<u64> = (0..16).map(|_| rng.val()).collect();
        for (r, v) in [7usize, 6, 2, 1, 8, 9].iter().zip(&args) {
            regs[*r] = *v;
        }
        regs[4] = WINDOW + 0x9008 + 16 * rng.below(0x6ff);
        let flags: Vec<u64> = (0..7)
            .map(|k| if k == 6 { 0 } else { rng.next_u64() & 1 })
            .collect();
        let useed = rng.next_u64();
        let ret0 = u64::from_le_bytes(fill[(regs[4] - WINDOW) as usize..][..8].try_into()?);
        // (1) P-mem reference
        let mut pm = PageMem::default();
        pm.write(CODE_BASE, &suite.code);
        pm.write(WINDOW, &fill);
        let mut h = Host::new(Box::new(pm));
        h.undef = Undef::Random(useed);
        let mut s = Sim::new(
            engine,
            &harness::load_module(engine, &super::sim_path("g"))?,
            h,
        )?;
        for l in 0..16 {
            s.set(l, regs[l as usize]);
        }
        for k in 0..7 {
            s.set(17 + k, flags[k as usize]);
        }
        s.set(RIP, entry);
        let mut n = 0u64;
        loop {
            let st = s.step();
            if st != 0 {
                bail!("P-mem status {st} {:?}", s.fault);
            }
            n += 1;
            if s.get(RIP) == ret0 && s.get(4) == regs[4] + 8 {
                break;
            }
            if n > 50_000_000 {
                bail!("P-mem: no return");
            }
        }
        let refo = Outcome {
            regs: (0..16).chain(17..23).map(|l| s.get(l)).collect(),
            window: {
                let mut v = vec![0u8; WINDOW_LEN as usize];
                for (i, b) in v.iter_mut().enumerate() {
                    *b = s.store.data_mut().mem.load(WINDOW + i as u64, 1).unwrap() as u8;
                }
                v
            },
        };
        // (2) closed problem
        let params: Vec<Val> = regs
            .iter()
            .chain(flags.iter())
            .map(|v| Val::I64(*v as i64))
            .collect();
        let mut store = Store::new(engine, Host::new(Box::new(PageMem::default())));
        store.data_mut().undef = Undef::Random(useed);
        let mem =
            Memory::new(&mut store, MemoryType::new(2, None)).map_err(|e| anyhow!("{e:?}"))?;
        mem.data_mut(&mut store)[..WINDOW_LEN as usize].copy_from_slice(&fill);
        let mut linker = Linker::new(engine);
        harness::add_env(&mut linker)?;
        linker
            .define(&mut store, "env", "mem", mem)
            .map_err(|e| anyhow!("{e:?}"))?;
        let inst = linker
            .instantiate(&mut store, &closed_m)
            .map_err(|e| anyhow!("{e:?}"))?;
        let f = inst.get_func(&mut store, &c.name).context("wrapper")?;
        f.call(&mut store, &params, &mut [])
            .map_err(|e| anyhow!("closed problem trapped: {e:?}"))?;
        let get = inst
            .get_typed_func::<i32, i64>(&mut store, "get")
            .map_err(|e| anyhow!("{e:?}"))?;
        let co = Outcome {
            regs: (0..16)
                .chain(17..23)
                .map(|l| get.call(&mut store, l).unwrap() as u64)
                .collect(),
            window: mem.data(&store)[..WINDOW_LEN as usize].to_vec(),
        };
        // (3) split modules linked to one simulator
        let mut pm = PageMem::default();
        pm.write(WINDOW, &fill);
        let mut h = Host::new(Box::new(pm));
        h.undef = Undef::Random(useed);
        let mut store = Store::new(engine, h);
        let mut linker = Linker::new(engine);
        harness::add_env(&mut linker)?;
        let si = linker
            .instantiate(&mut store, sim_m)
            .map_err(|e| anyhow!("{e:?}"))?;
        linker
            .instance(&mut store, "sim", si)
            .map_err(|e| anyhow!("{e:?}"))?;
        let mut root = None;
        for (n, m) in &split_ms {
            let i = linker
                .instantiate(&mut store, m)
                .map_err(|e| anyhow!("link {n}: {e:?}"))?;
            linker
                .instance(&mut store, n, i)
                .map_err(|e| anyhow!("{e:?}"))?;
            root = Some(i);
        }
        let mut ss = Sim::from_instance(store, si)?;
        for l in 0..16 {
            ss.set(l, regs[l as usize]);
        }
        for k in 0..7 {
            ss.set(17 + k, flags[k as usize]);
        }
        ss.set(RIP, entry);
        let rf = root
            .unwrap()
            .get_typed_func::<(), i32>(&mut ss.store, &c.name)
            .map_err(|e| anyhow!("{e:?}"))?;
        let st = rf
            .call(&mut ss.store, ())
            .map_err(|e| anyhow!("split trapped: {e:?}"))?;
        if st != 0 || ss.get(RIP) != ret0 {
            bail!("split: status {st}, rip {:#x}", ss.get(RIP));
        }
        let so = Outcome {
            regs: (0..16).chain(17..23).map(|l| ss.get(l)).collect(),
            window: (0..WINDOW_LEN)
                .map(|i| ss.store.data_mut().mem.load(WINDOW + i, 1).unwrap() as u8)
                .collect(),
        };
        for (what, o) in [("closed", &co), ("split", &so)] {
            if o.regs != refo.regs {
                let d: Vec<String> = (0..22)
                    .filter(|&i| o.regs[i] != refo.regs[i])
                    .map(|i| {
                        format!(
                            "{}: {:#x} vs {:#x}",
                            NAMES[if i < 16 { i } else { i + 1 }],
                            o.regs[i],
                            refo.regs[i]
                        )
                    })
                    .collect();
                bail!(
                    "{what} differs from P-mem (args {args:x?}): {}",
                    d.join(", ")
                );
            }
            if o.window != refo.window {
                bail!("{what}: memory differs from P-mem");
            }
        }
        // (4) z3 on the concrete pair
        let mut ranges = vec![(regs[4] - c.frame, regs[4] + 8)];
        for (k, v) in kinds.iter().zip(&args) {
            if matches!(k, Arg::Str | Arg::Str2 | Arg::Buf(_)) {
                ranges.push((v.saturating_sub(16), v + 0x400));
            }
        }
        smt += "(push)\n";
        for (i, n) in NAMES[..16].iter().enumerate() {
            writeln!(
                smt,
                "(define-fun old_{n} () (_ BitVec 64) #x{:016x})",
                regs[i]
            )?;
            writeln!(
                smt,
                "(define-fun new_{n} () (_ BitVec 64) #x{:016x})",
                co.regs[i]
            )?;
        }
        for (k, n) in FLAGS[..6].iter().enumerate() {
            writeln!(
                smt,
                "(define-fun old_{n} () (_ BitVec 64) #x{:016x})",
                flags[k]
            )?;
            writeln!(
                smt,
                "(define-fun new_{n} () (_ BitVec 64) #x{:016x})",
                co.regs[16 + k]
            )?;
        }
        smt += &smt_bytes("old", WINDOW, &fill, &ranges);
        smt += &smt_bytes("new", WINDOW, &co.window, &ranges);
        for d in defs.values() {
            smt += &term_smt(d).unwrap_or_else(|_| d.clone());
            smt += "\n";
        }
        writeln!(
            smt,
            "(push)\n(assert {req})\n(check-sat)\n(pop)\n(assert (and {req} (not {ens})))\n(check-sat)\n(pop)"
        )?;
        z3_cases += 1;
    }
    let p = std::env::temp_dir().join(format!(
        "wasm-sim-contract-{}-{}.smt2",
        c.name,
        std::process::id()
    ));
    std::fs::write(&p, &smt)?;
    let out = std::process::Command::new("z3")
        .arg("-T:120")
        .arg(&p)
        .output()?;
    let o = String::from_utf8_lossy(&out.stdout);
    let ls: Vec<&str> = o.lines().collect();
    // answers come in pairs: (requires satisfiable?, requires and not ensures)
    let nonvacuous = ls.iter().step_by(2).filter(|l| **l == "sat").count();
    let unsat = ls
        .iter()
        .skip(1)
        .step_by(2)
        .filter(|l| **l == "unsat")
        .count();
    if unsat != z3_cases || ls.len() != 2 * z3_cases {
        let first = ls
            .iter()
            .skip(1)
            .step_by(2)
            .find(|l| **l != "unsat")
            .unwrap_or(&"");
        bail!(
            "z3: {unsat}/{z3_cases} unsat, first other answer: {first} (smt kept in {})",
            p.display()
        );
    }
    let _ = std::fs::remove_file(&p);
    let _ = pcalls::Opts::default();
    Ok(format!(
        "{per} random entry states: closed = split = P-mem; z3: contract holds on all {z3_cases} ({nonvacuous} satisfy requires)"
    ))
}
