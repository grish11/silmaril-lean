//! Annotated WAT problems as produced by the reductions: an exported function
//! preceded by `;; @requires P` and `;; @ensures Q` (SMT-LIB), loops
//! annotated with `;; @invariant I` / `;; @decreases M`, file-level
//! `;; @define` definitions and callee contracts `;; @assume`. Three flavours:
//!
//! * RV64 P-locals (`wasm-sim-rv reduce`): parameters are the entry values of
//!   registers by ABI name, `result` the first result; memory `env.memory`
//!   (RV address = Wasm address); callees `@assume g requires P` /
//!   `@assume g ensures Q` over the callee's parameter names and `result`.
//! * x86 closed (`wasm-sim problems`, `closed/`): the wrapper takes every GPR
//!   and flag; `(old (reg r))` is the entry value, `(reg r)` the final
//!   simulator state; memory `env.mem` is the window at guest 0x100000.
//! * x86 split (`split/<f>/`): the function runs on the shared simulator
//!   `../sim.wat` from an arbitrary state, memory through `mem.*` imports (one
//!   environment memory); callees `@assume g (=> P Q)` over `(old (reg r))`
//!   and `(reg r)`; the function must return status 0.
//!
//! `(memN a)` reads N bits little-endian from the memory after the call,
//! `(old (memN a))` before. A sibling `<name>.spec` may supply loop annotations.

use super::problem::{ContractSpec, LoopAnn, ModSpec, Problem};
use crate::sexp::{self, Sexp};
use anyhow::{Context, Result, bail};
use std::path::Path;

fn after<'a>(line: &'a str, key: &str) -> Option<&'a str> {
    let t = line.trim_start();
    let t = t.strip_prefix(";;")?.trim_start();
    t.strip_prefix(key).map(str::trim)
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Flavor {
    Rv64,
    X86Closed,
    X86Split,
}

pub const X86_REGS: [(&str, &str); 24] = [
    ("rax", "r0"),
    ("rcx", "r1"),
    ("rdx", "r2"),
    ("rbx", "r3"),
    ("rsp", "r4"),
    ("rbp", "r5"),
    ("rsi", "r6"),
    ("rdi", "r7"),
    ("r8", "r8"),
    ("r9", "r9"),
    ("r10", "r10"),
    ("r11", "r11"),
    ("r12", "r12"),
    ("r13", "r13"),
    ("r14", "r14"),
    ("r15", "r15"),
    ("rip", "rip"),
    ("cf", "cf"),
    ("pf", "pf"),
    ("af", "af"),
    ("zf", "zf"),
    ("sf", "sf"),
    ("of", "of"),
    ("df", "df"),
];

pub fn is_flag(r: &str) -> bool {
    matches!(r, "cf" | "pf" | "af" | "zf" | "sf" | "of" | "df")
}

/// How names and memory accesses of a contract formula are rendered.
struct Names<'a> {
    flavor: Flavor,
    /// Register value: (register, old?) to SMT text.
    reg: &'a dyn Fn(&str, bool) -> String,
    mem_old: &'a str,
    mem_new: &'a str,
    results: &'a [String],
}

fn addr(n: &Names, a: &str, k: u32) -> String {
    let a = if k == 0 {
        a.to_string()
    } else {
        format!("(bvadd {a} (_ bv{k} 64))")
    };
    match n.flavor {
        Flavor::X86Closed => format!("((_ extract 31 0) (bvsub {a} #x0000000000100000))"),
        Flavor::X86Split => a,
        Flavor::Rv64 => format!("((_ extract 31 0) {a})"),
    }
}

fn tr(s: &Sexp, n: &Names, old: bool) -> Result<String> {
    let Sexp::List(l) = s else {
        return Ok(s.to_string());
    };
    let head = l.first().and_then(Sexp::atom);
    match head {
        Some("old") if l.len() == 2 => tr(&l[1], n, true),
        Some("reg") if l.len() == 2 => {
            let r = l[1].atom().context("(reg r)")?;
            Ok((n.reg)(r, old))
        }
        Some("result") if l.len() == 2 => {
            let r = l[1].atom().context("(result r)")?;
            let k = n
                .results
                .iter()
                .position(|x| x == r)
                .with_context(|| format!("unknown result {r}"))?;
            Ok(if k == 0 {
                "result".into()
            } else {
                format!("result{k}")
            })
        }
        Some(m @ ("mem8" | "mem16" | "mem32" | "mem64")) if l.len() == 2 => {
            let bytes: u32 = m[3..].parse::<u32>()? / 8;
            let a = tr(&l[1], n, old)?;
            let mem = if old { n.mem_old } else { n.mem_new };
            let mut parts = Vec::new();
            for k in (0..bytes).rev() {
                parts.push(format!("(select {mem} {})", addr(n, &a, k)));
            }
            Ok(if parts.len() == 1 {
                parts.pop().unwrap()
            } else {
                format!("(concat {})", parts.join(" "))
            })
        }
        _ => {
            let parts: Vec<String> = l.iter().map(|x| tr(x, n, old)).collect::<Result<_>>()?;
            Ok(format!("({})", parts.join(" ")))
        }
    }
}

fn translate(text: &str, n: &Names) -> Result<String> {
    let s = sexp::parse(text).with_context(|| format!("parsing {text}"))?;
    tr(&s, n, false)
}

/// Standard definitions of the spec functions the reductions use (64-bit;
/// `mem64` reads the memory on entry). `popcount` is the non-recursive sum of
/// the bits (equal to the recursive definition, and decidable by bit-blasting).
pub fn standard_def(name: &str) -> Option<&'static str> {
    Some(match name {
        "fact" => {
            "(define-fun-rec fact ((n (_ BitVec 64))) (_ BitVec 64) (ite (bvule n #x0000000000000001) #x0000000000000001 (bvmul n (fact (bvsub n #x0000000000000001)))))"
        }
        "fib" => {
            "(define-fun-rec fib ((n (_ BitVec 64))) (_ BitVec 64) (ite (bvule n #x0000000000000001) n (bvadd (fib (bvsub n #x0000000000000001)) (fib (bvsub n #x0000000000000002)))))"
        }
        "gcd" => {
            "(define-fun-rec gcd ((a (_ BitVec 64)) (b (_ BitVec 64))) (_ BitVec 64) (ite (= b #x0000000000000000) a (gcd b (bvurem a b))))"
        }
        "popcount" => {
            "(define-fun popcount ((x (_ BitVec 64))) (_ BitVec 64) (bvadd ((_ zero_extend 63) ((_ extract 0 0) x)) ((_ zero_extend 63) ((_ extract 1 1) x)) ((_ zero_extend 63) ((_ extract 2 2) x)) ((_ zero_extend 63) ((_ extract 3 3) x)) ((_ zero_extend 63) ((_ extract 4 4) x)) ((_ zero_extend 63) ((_ extract 5 5) x)) ((_ zero_extend 63) ((_ extract 6 6) x)) ((_ zero_extend 63) ((_ extract 7 7) x)) ((_ zero_extend 63) ((_ extract 8 8) x)) ((_ zero_extend 63) ((_ extract 9 9) x)) ((_ zero_extend 63) ((_ extract 10 10) x)) ((_ zero_extend 63) ((_ extract 11 11) x)) ((_ zero_extend 63) ((_ extract 12 12) x)) ((_ zero_extend 63) ((_ extract 13 13) x)) ((_ zero_extend 63) ((_ extract 14 14) x)) ((_ zero_extend 63) ((_ extract 15 15) x)) ((_ zero_extend 63) ((_ extract 16 16) x)) ((_ zero_extend 63) ((_ extract 17 17) x)) ((_ zero_extend 63) ((_ extract 18 18) x)) ((_ zero_extend 63) ((_ extract 19 19) x)) ((_ zero_extend 63) ((_ extract 20 20) x)) ((_ zero_extend 63) ((_ extract 21 21) x)) ((_ zero_extend 63) ((_ extract 22 22) x)) ((_ zero_extend 63) ((_ extract 23 23) x)) ((_ zero_extend 63) ((_ extract 24 24) x)) ((_ zero_extend 63) ((_ extract 25 25) x)) ((_ zero_extend 63) ((_ extract 26 26) x)) ((_ zero_extend 63) ((_ extract 27 27) x)) ((_ zero_extend 63) ((_ extract 28 28) x)) ((_ zero_extend 63) ((_ extract 29 29) x)) ((_ zero_extend 63) ((_ extract 30 30) x)) ((_ zero_extend 63) ((_ extract 31 31) x)) ((_ zero_extend 63) ((_ extract 32 32) x)) ((_ zero_extend 63) ((_ extract 33 33) x)) ((_ zero_extend 63) ((_ extract 34 34) x)) ((_ zero_extend 63) ((_ extract 35 35) x)) ((_ zero_extend 63) ((_ extract 36 36) x)) ((_ zero_extend 63) ((_ extract 37 37) x)) ((_ zero_extend 63) ((_ extract 38 38) x)) ((_ zero_extend 63) ((_ extract 39 39) x)) ((_ zero_extend 63) ((_ extract 40 40) x)) ((_ zero_extend 63) ((_ extract 41 41) x)) ((_ zero_extend 63) ((_ extract 42 42) x)) ((_ zero_extend 63) ((_ extract 43 43) x)) ((_ zero_extend 63) ((_ extract 44 44) x)) ((_ zero_extend 63) ((_ extract 45 45) x)) ((_ zero_extend 63) ((_ extract 46 46) x)) ((_ zero_extend 63) ((_ extract 47 47) x)) ((_ zero_extend 63) ((_ extract 48 48) x)) ((_ zero_extend 63) ((_ extract 49 49) x)) ((_ zero_extend 63) ((_ extract 50 50) x)) ((_ zero_extend 63) ((_ extract 51 51) x)) ((_ zero_extend 63) ((_ extract 52 52) x)) ((_ zero_extend 63) ((_ extract 53 53) x)) ((_ zero_extend 63) ((_ extract 54 54) x)) ((_ zero_extend 63) ((_ extract 55 55) x)) ((_ zero_extend 63) ((_ extract 56 56) x)) ((_ zero_extend 63) ((_ extract 57 57) x)) ((_ zero_extend 63) ((_ extract 58 58) x)) ((_ zero_extend 63) ((_ extract 59 59) x)) ((_ zero_extend 63) ((_ extract 60 60) x)) ((_ zero_extend 63) ((_ extract 61 61) x)) ((_ zero_extend 63) ((_ extract 62 62) x)) ((_ zero_extend 63) ((_ extract 63 63) x))))"
        }
        "tri" => {
            "(define-fun tri ((x (_ BitVec 64))) (_ BitVec 64) (bvudiv (bvmul x (bvadd x #x0000000000000001)) #x0000000000000002))"
        }
        "sumarr" => {
            "(define-fun-rec sumarr ((p (_ BitVec 64)) (n (_ BitVec 64))) (_ BitVec 64) (ite (bvsle n #x0000000000000000) #x0000000000000000 (bvadd (old (mem64 p)) (sumarr (bvadd p #x0000000000000008) (bvsub n #x0000000000000001)))))"
        }
        "sumsq" => {
            "(define-fun-rec sumsq ((p (_ BitVec 64)) (n (_ BitVec 64))) (_ BitVec 64) (ite (bvsle n #x0000000000000000) #x0000000000000000 (bvadd (bvmul (old (mem64 p)) (old (mem64 p))) (sumsq (bvadd p #x0000000000000008) (bvsub n #x0000000000000001)))))"
        }
        _ => return None,
    })
}

/// `name: params ["a0"] -> results ["a0", "a1"]` comments of RV64 callees.
fn sig_comment(line: &str) -> Option<(String, Vec<String>, Vec<String>)> {
    let t = line.trim_start().strip_prefix(";;")?.trim();
    let (name, rest) = t.split_once(": params ")?;
    let (ps, rs) = rest.split_once(" -> results ")?;
    let list = |x: &str| -> Vec<String> {
        x.trim()
            .trim_start_matches('[')
            .trim_end_matches(']')
            .split(',')
            .map(|y| y.trim().trim_matches('"').to_string())
            .filter(|y| !y.is_empty())
            .collect()
    };
    Some((name.to_string(), list(ps), list(rs)))
}

pub fn problem_of_wat(path: &Path) -> Result<Problem> {
    let src = std::fs::read_to_string(path)?;
    let dir = path.parent().unwrap_or(Path::new("."));
    let flavor = if src.contains("(import \"env\" \"mem\" (memory") {
        Flavor::X86Closed
    } else if dir.join("link.json").is_file() {
        Flavor::X86Split
    } else {
        Flavor::Rv64
    };
    let mut requires = Vec::new();
    let mut ensures = Vec::new();
    let mut defines = Vec::new();
    let mut func: Option<String> = None;
    let mut pending = false;
    let mut loops: Vec<LoopAnn> = Vec::new();
    let mut cur_fn: Option<String> = None;
    let mut loop_count: i64 = 0;
    // callee contracts: (import name, requires, ensures) and signatures
    let mut assumes: Vec<(String, Option<String>, Option<String>)> = Vec::new();
    let mut sigs: Vec<(String, Vec<String>, Vec<String>)> = Vec::new();
    let mut last_assume: Option<String> = None;
    let mut imports: Vec<(String, String)> = Vec::new(); // (module.name, after which assume)
    for line in src.lines() {
        if let Some(i) = line.find("(import \"") {
            let rest = &line[i + 9..];
            if let Some((md, r2)) = rest.split_once('"') {
                let nm = r2.trim_start().trim_start_matches('"');
                let nm: String = nm.chars().take_while(|c| *c != '"').collect();
                if let Some(a) = last_assume.take() {
                    imports.push((format!("{md}.{nm}"), a));
                }
            }
        }
        if let Some(i) = line.find("(func $")
            && !line.contains("(import")
        {
            let name: String = line[i + 7..]
                .chars()
                .take_while(|c| !c.is_whitespace() && *c != ')' && *c != '(')
                .collect();
            cur_fn = Some(name.clone());
            loop_count = 0;
            if pending && func.is_none() {
                func = Some(name);
                pending = false;
            }
        }
        loop_count += line.matches("(loop").count() as i64;
        if let Some(sg) = sig_comment(line) {
            sigs.push(sg);
        }
        if let Some(d) = after(line, "@define") {
            defines.push(d.to_string());
        } else if let Some(a) = after(line, "@assume") {
            let (name, rest) = a.split_once(char::is_whitespace).context("@assume g …")?;
            let rest = rest.trim();
            let e = match assumes.iter_mut().find(|x| x.0 == name) {
                Some(e) => e,
                None => {
                    assumes.push((name.to_string(), None, None));
                    assumes.last_mut().unwrap()
                }
            };
            if let Some(r) = rest.strip_prefix("requires ") {
                e.1 = Some(r.to_string());
            } else if let Some(r) = rest.strip_prefix("ensures ") {
                e.2 = Some(r.to_string());
            } else {
                // `(=> P Q)`, or Q alone
                let s = sexp::parse(rest)?;
                match s.list() {
                    Some([Sexp::Atom(i), p, q]) if i == "=>" => {
                        e.1 = Some(p.to_string());
                        e.2 = Some(q.to_string());
                    }
                    _ => e.2 = Some(rest.to_string()),
                }
            }
            last_assume = Some(name.to_string());
        } else if let Some(r) = after(line, "@requires") {
            requires.push(r.to_string());
            pending = true;
        } else if let Some(e) = after(line, "@ensures") {
            ensures.push(e.to_string());
            pending = true;
        } else if let Some(inv) = after(line, "@invariant") {
            if inv != "TODO" && !inv.is_empty() {
                let f = cur_fn.clone().context("@invariant outside a function")?;
                loops.push(LoopAnn {
                    func: format!("${f}"),
                    r#loop: (loop_count - 1).max(0) as u32,
                    invariant: inv.to_string(),
                    decreases: None,
                    parts: vec![],
                    measures: vec![],
                });
            }
        } else if let Some(d) = after(line, "@decreases") {
            let f = cur_fn.clone().context("@decreases outside a function")?;
            let k = (loop_count - 1).max(0) as u32;
            if let Some(l) = loops
                .iter_mut()
                .find(|l| l.func == format!("${f}") && l.r#loop == k)
            {
                l.decreases = Some(d.to_string());
            }
        }
    }
    let func = func.context("no function with @requires/@ensures")?;
    // the exported function of a split piece: the export of `func` if any
    let stem = path.file_stem().unwrap().to_string_lossy().to_string();
    for cand in [
        dir.join(format!("{stem}.spec")),
        dir.join("..").join(format!("{stem}.spec")),
    ] {
        if let Ok(spec) = std::fs::read_to_string(&cand) {
            for line in spec.lines() {
                let mut it = line.splitn(3, ' ');
                let (Some(key), Some(k), Some(rest)) = (it.next(), it.next(), it.next()) else {
                    continue;
                };
                let Ok(k) = k.parse::<u32>() else { continue };
                let f = format!("${func}");
                match key {
                    "invariant" if !loops.iter().any(|l| l.func == f && l.r#loop == k) => {
                        loops.push(LoopAnn {
                            func: f,
                            r#loop: k,
                            invariant: rest.to_string(),
                            decreases: None,
                            parts: vec![],
                            measures: vec![],
                        });
                    }
                    "decreases" => {
                        if let Some(l) = loops.iter_mut().find(|l| l.func == f && l.r#loop == k)
                            && l.decreases.is_none()
                        {
                            l.decreases = Some(rest.to_string());
                        }
                    }
                    _ => {}
                }
            }
            break;
        }
    }
    let x86_reg = |r: &str| -> Result<&'static str> {
        X86_REGS
            .iter()
            .find(|x| x.0 == r)
            .map(|x| x.1)
            .with_context(|| format!("unknown register {r}"))
    };
    let glob = |prefix: &str, r: &str| -> String {
        let g = x86_reg(r).unwrap_or("?");
        if is_flag(r) {
            format!("((_ zero_extend 32) {prefix}g.{g})")
        } else {
            format!("{prefix}g.{g}")
        }
    };
    let reg_main = |r: &str, old: bool| -> String {
        match (flavor, old) {
            (Flavor::X86Closed, true) => r.to_string(),
            (Flavor::X86Split, true) => glob("", r),
            (_, false) => glob("post.", r),
            (Flavor::Rv64, true) => r.to_string(),
        }
    };
    let entry_results = Vec::new();
    let main = Names {
        flavor,
        reg: &reg_main,
        mem_old: "|mem!old|",
        mem_new: "|mem!post|",
        results: &entry_results,
    };
    let requires: Vec<String> = requires
        .iter()
        .map(|r| translate(r, &main))
        .collect::<Result<_>>()?;
    let mut ensures: Vec<String> = ensures
        .iter()
        .map(|r| translate(r, &main))
        .collect::<Result<_>>()?;
    // uninterpreted spec functions with a standard meaning get their definition
    let defines: Vec<String> = defines
        .iter()
        .map(|d| {
            let d = match d
                .strip_prefix("(declare-fun ")
                .and_then(|r| r.split_whitespace().next())
            {
                Some(n) => standard_def(n)
                    .map(str::to_string)
                    .unwrap_or_else(|| d.clone()),
                None => d.clone(),
            };
            translate(&d, &main)
        })
        .collect::<Result<_>>()?;
    for l in &mut loops {
        l.invariant = translate(&l.invariant, &main)?;
    }
    // callee contracts
    let reg_callee = |r: &str, old: bool| {
        if old {
            format!("old.{r}")
        } else {
            r.to_string()
        }
    };
    let mut contracts = Vec::new();
    for (name, pre, post) in &assumes {
        let import = imports
            .iter()
            .find(|(_, a)| a == name)
            .map(|x| x.0.clone())
            .unwrap_or_else(|| format!("{name}.{name}"));
        let (params, results) = sigs
            .iter()
            .find(|s| &s.0 == name)
            .map(|s| (s.1.clone(), s.2.clone()))
            .unwrap_or_else(|| (vec!["a0".into()], vec!["a0".into()]));
        let n = Names {
            flavor,
            reg: &reg_callee,
            mem_old: "cmem!old",
            mem_new: "cmem!new",
            results: &results,
        };
        let pre = translate(pre.as_deref().unwrap_or("true"), &n)?;
        let post = translate(post.as_deref().unwrap_or("true"), &n)?;
        if pre.contains("cmem!") || post.contains("cmem!") {
            bail!("callee contracts over memory are not supported ({name})");
        }
        contracts.push(ContractSpec {
            import,
            name: name.clone(),
            pre,
            post,
            style: if flavor == Flavor::Rv64 {
                "values".into()
            } else {
                "x86".into()
            },
            params,
            results,
        });
    }
    let mut p: Problem = toml::from_str("kind = \"post\"\nno_trap = true\n")?;
    p.name = Some(stem);
    p.entry = Some(format!("${func}"));
    p.modules = vec![ModSpec {
        name: "m".into(),
        wat: path.file_name().unwrap().to_string_lossy().to_string(),
    }];
    match flavor {
        Flavor::X86Split => {
            let link: serde_json::Value =
                serde_json::from_str(&std::fs::read_to_string(dir.join("link.json"))?)?;
            let sim = link
                .get("sim")
                .and_then(|x| x.as_str())
                .unwrap_or("../sim.wat");
            p.modules.insert(
                0,
                ModSpec {
                    name: "sim".into(),
                    wat: sim.to_string(),
                },
            );
            p.init = Some("symbolic".into());
            p.env.mem = Some("array".into());
            p.mem_obs = Some("env".into());
            ensures.push("(= result #x00000000)".into());
        }
        Flavor::X86Closed => {
            p.init = Some("module".into());
            p.mem_obs = Some("env.mem".into());
        }
        Flavor::Rv64 => {
            p.init = Some("module".into());
            if src.contains("(import \"env\" \"memory\" (memory") {
                p.mem_obs = Some("env.memory".into());
            }
        }
    }
    p.pre = requires;
    p.post = ensures;
    p.loops = loops;
    p.defines = defines;
    p.contracts = contracts;
    Ok(p)
}
