//! `wasm-vc reflect`: annotated WAT to the reflective VC generator of
//! `Silmaril.Wasm.Auto.VCGen` (docs/wasm-auto-verify.md, track vcgen).
//!
//! The tool only translates and runs: it reads the annotations of one
//! function (`@requires`, `@ensures`, `@invariant` per loop, in source order),
//! writes them as a Lean `FnSpec` next to the quoted program, lets Lean compute
//! the verification conditions (`genFunc`, verified once by `genFunc_sound`),
//! sends each condition to z3 as printed by Lean (`smtScript`: comparisons are
//! interpreted `ite`s on 32 and 64 bits, so a model is a real counterexample
//! unless the condition uses specification functions), and tries candidate
//! tactics on the conditions in Lean. Nothing it does is trusted.

use crate::sexp::{self, Sexp};
use anyhow::{Context, Result, bail};
use serde::Deserialize;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

/// `reflect.toml`.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Config {
    /// Lean name of the generated declarations (`<name>Spec`, `<name>_vcs`, …).
    pub name: String,
    /// The annotated WAT file, relative to the configuration.
    pub source: String,
    /// The function to verify (`$name` without `$`).
    pub func: String,
    /// The generator's fuel.
    #[serde(default = "default_fuel")]
    pub fuel: u32,
    /// Extra Lean imports (lemmas used by `tactics`).
    #[serde(default)]
    pub imports: Vec<String>,
    /// Specification functions.
    #[serde(default)]
    pub fun: Vec<Fun>,
    /// Extra candidate tactics, tried first on every condition.
    #[serde(default)]
    pub tactics: Vec<String>,
    /// The generator: `1` is `Silmaril.Wasm.Auto.VCGen` (pass 1, SMT printer `VCSmt`), `2` is
    /// `Silmaril.Wasm.Auto.VCGen2` (SSA names, memory, calls; SMT printer `VCSmt2`: memories as
    /// arrays with a size).
    #[serde(default = "one_u32")]
    pub generator: u32,
    /// The function uses memory `0` (generator 2 only).
    #[serde(default)]
    pub memory: bool,
}

fn one_u32() -> u32 {
    1
}

fn default_fuel() -> u32 {
    1000
}

/// A unary (`arity = 1`) or binary specification function on `i32` or `i64`.
#[derive(Debug, Deserialize, Clone)]
#[serde(deny_unknown_fields)]
pub struct Fun {
    pub name: String,
    pub ty: String,
    #[serde(default = "one")]
    pub arity: usize,
    pub lean: String,
}

fn one() -> usize {
    1
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Ty {
    I32,
    I64,
}

impl Ty {
    fn parse(s: &str) -> Result<Ty> {
        match s {
            "i32" => Ok(Ty::I32),
            "i64" => Ok(Ty::I64),
            _ => bail!("only i32 and i64 values are supported, not {s}"),
        }
    }
    fn lean(self) -> &'static str {
        match self {
            Ty::I32 => ".i32",
            Ty::I64 => ".i64",
        }
    }
}

/// The function's signature and annotations.
#[derive(Debug)]
pub struct Target {
    /// Position among the module's defined functions.
    pub index: usize,
    pub params: Vec<(Option<String>, Ty)>,
    pub locals: Vec<(Option<String>, Ty)>,
    pub results: Vec<Ty>,
    pub requires: Vec<Sexp>,
    pub ensures: Vec<Sexp>,
    pub invariants: Vec<Sexp>,
}

fn decls(x: &Sexp) -> Result<Vec<(Option<String>, Ty)>> {
    let l = x.list().unwrap_or_default();
    let rest = &l[1..];
    if let Some(n) = rest
        .first()
        .and_then(Sexp::atom)
        .and_then(|a| a.strip_prefix('$'))
    {
        let t = rest.get(1).and_then(Sexp::atom).context("missing type")?;
        return Ok(vec![(Some(n.to_string()), Ty::parse(t)?)]);
    }
    rest.iter()
        .map(|t| Ok((None, Ty::parse(t.atom().context("bad type")?)?)))
        .collect()
}

/// Read the target function of an annotated module.
pub fn target(src: &str, func: &str) -> Result<Target> {
    let (top, anns) = sexp::parse_with_annotations(src)?;
    let fields = match top.list() {
        Some([Sexp::Atom(m), rest @ ..]) if m == "module" => rest,
        _ => bail!("expected (module …)"),
    };
    let offsets = sexp::func_offsets(src);
    let funcs: Vec<&Sexp> = fields.iter().filter(|f| f.head() == Some("func")).collect();
    if funcs.len() != offsets.len() {
        bail!("could not locate the functions in the source");
    }
    let index = funcs
        .iter()
        .position(|f| {
            f.list().and_then(|l| l.get(1)).and_then(Sexp::atom) == Some(&format!("${func}"))
        })
        .with_context(|| format!("no function ${func}"))?;
    let l = funcs[index].list().unwrap_or_default();
    let (mut params, mut locals, mut results) = (Vec::new(), Vec::new(), Vec::new());
    for x in &l[2..] {
        match x.head() {
            Some("param") => params.extend(decls(x)?),
            Some("local") => locals.extend(decls(x)?),
            Some("result") => {
                for t in &x.list().unwrap_or_default()[1..] {
                    results.push(Ty::parse(t.atom().context("bad result type")?)?);
                }
            }
            _ => {}
        }
    }
    let start = offsets[index];
    let prev = if index == 0 { 0 } else { offsets[index - 1] };
    let next = offsets.get(index + 1).copied().unwrap_or(src.len());
    let (mut requires, mut ensures, mut invariants) = (Vec::new(), Vec::new(), Vec::new());
    for a in &anns {
        let parsed = || sexp::parse(&a.text).with_context(|| format!("@{} {}", a.key, a.text));
        if a.offset < start && a.offset >= prev {
            match a.key.as_str() {
                "requires" => requires.push(parsed()?),
                "ensures" => ensures.push(parsed()?),
                _ => {}
            }
        } else if a.offset >= start && a.offset < next && a.key == "invariant" {
            invariants.push(parsed()?);
        }
    }
    Ok(Target {
        index,
        params,
        locals,
        results,
        requires,
        ensures,
        invariants,
    })
}

/// Where an annotation is read: the precondition, the postcondition or an invariant.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Pre,
    Post,
    Inv,
}

struct Tr<'a> {
    t: &'a Target,
    funs: &'a [Fun],
    mode: Mode,
    /// Memory annotations (`load`, `old_load`, `inbounds`) are allowed (generator 2).
    memory: bool,
}

fn lit(a: &str) -> Option<(u128, Ty)> {
    let h = a.strip_prefix("#x")?;
    let v = u128::from_str_radix(h, 16).ok()?;
    match h.len() {
        8 => Some((v, Ty::I32)),
        16 => Some((v, Ty::I64)),
        _ => None,
    }
}

const BIN: [(&str, &str); 13] = [
    ("bvadd", ".add"),
    ("bvsub", ".sub"),
    ("bvmul", ".mul"),
    ("bvand", ".and"),
    ("bvor", ".or"),
    ("bvxor", ".xor"),
    ("bvshl", ".shl"),
    ("bvlshr", "(.shr .unsigned)"),
    ("bvashr", "(.shr .signed)"),
    ("bvudiv", "(.div .unsigned)"),
    ("bvsdiv", "(.div .signed)"),
    ("bvurem", "(.rem .unsigned)"),
    ("bvsrem", "(.rem .signed)"),
];

const REL: [(&str, &str); 10] = [
    ("=", ".eq"),
    ("distinct", ".ne"),
    ("bvult", "(.lt .unsigned)"),
    ("bvule", "(.le .unsigned)"),
    ("bvugt", "(.gt .unsigned)"),
    ("bvuge", "(.ge .unsigned)"),
    ("bvslt", "(.lt .signed)"),
    ("bvsle", "(.le .signed)"),
    ("bvsgt", "(.gt .signed)"),
    ("bvsge", "(.ge .signed)"),
];

impl Tr<'_> {
    fn var(&self, name: &str, old: bool) -> Result<(String, Ty)> {
        if name == "result" {
            if self.mode != Mode::Post || self.t.results.len() != 1 {
                bail!("`result` is only allowed in @ensures of a one-result function");
            }
            let t = self.t.results[0];
            return Ok((format!("(.loc {} 0)", t.lean()), t));
        }
        let all: Vec<_> = self.t.params.iter().chain(&self.t.locals).collect();
        let j = all
            .iter()
            .position(|(n, _)| n.as_deref() == Some(name))
            .with_context(|| format!("unknown variable {name}"))?;
        let t = all[j].1;
        let is_param = j < self.t.params.len();
        if self.mode == Mode::Inv && !old {
            Ok((format!("(.loc {} {j})", t.lean()), t))
        } else if is_param {
            Ok((format!("(.var {} {j})", t.lean()), t))
        } else {
            bail!("local {name} is only visible in @invariant")
        }
    }

    /// A term: Lean `Tm` syntax and its type.
    fn tm(&self, s: &Sexp) -> Result<(String, Ty)> {
        match s {
            Sexp::Atom(a) => {
                if let Some((v, t)) = lit(a) {
                    return Ok((format!("(.lit {} {v})", t.lean()), t));
                }
                self.var(a, false)
            }
            Sexp::List(l) => {
                let head = l.first().and_then(Sexp::atom).context("term head")?;
                let args = &l[1..];
                if head == "_" {
                    let v = args
                        .first()
                        .and_then(Sexp::atom)
                        .and_then(|a| a.strip_prefix("bv"));
                    let w = args.get(1).and_then(Sexp::atom);
                    let t = match w {
                        Some("32") => Ty::I32,
                        Some("64") => Ty::I64,
                        _ => bail!("only (_ bvN 32) and (_ bvN 64) literals"),
                    };
                    let v: u128 = v.context("literal")?.parse()?;
                    return Ok((format!("(.lit {} {v})", t.lean()), t));
                }
                if head == "old" {
                    let x = args.first().and_then(Sexp::atom).context("(old x)")?;
                    return self.var(x, true);
                }
                if head == "load" || head == "old_load" {
                    // `(load a)`: the `i32` at address `a` of the current memory (the final
                    // memory in @ensures, the memory at entry in @requires); `old_load`: at entry.
                    let [a] = args else {
                        bail!("{head} takes one argument")
                    };
                    let (a, ta) = self.tm(a)?;
                    if ta != Ty::I32 {
                        bail!("{head} takes an i32 address");
                    }
                    return Ok((
                        format!("(.load .i32 4 .unsigned {} {a} 0)", self.mr(head)?),
                        Ty::I32,
                    ));
                }
                if head == "ite" {
                    let [c, a, b] = args else {
                        bail!("ite takes three arguments")
                    };
                    let (a, ta) = self.tm(a)?;
                    let (b, tb) = self.tm(b)?;
                    if ta != tb {
                        bail!("ite branches of different types");
                    }
                    return Ok((format!("(.ite {} {a} {b})", self.cond(c)?), ta));
                }
                if head == "bvneg" {
                    let [a] = args else {
                        bail!("bvneg takes one argument")
                    };
                    let (a, t) = self.tm(a)?;
                    return Ok((format!("(.bin .sub (.lit {} 0) {a})", t.lean()), t));
                }
                if let Some((_, op)) = BIN.iter().find(|(n, _)| *n == head) {
                    let [a, b] = args else {
                        bail!("{head} takes two arguments")
                    };
                    let (a, ta) = self.tm(a)?;
                    let (b, tb) = self.tm(b)?;
                    if ta != tb {
                        bail!("{head} on different widths");
                    }
                    return Ok((format!("(.bin {op} {a} {b})"), ta));
                }
                if let Some(f) = self.funs.iter().find(|f| f.name == head) {
                    let t = Ty::parse(&f.ty)?;
                    let k = self
                        .funs
                        .iter()
                        .filter(|g| g.ty == f.ty && g.arity == f.arity)
                        .position(|g| g.name == f.name)
                        .unwrap_or(0);
                    let ts: Vec<String> = args
                        .iter()
                        .map(|a| {
                            let (s, ta) = self.tm(a)?;
                            if ta != t {
                                bail!("{head} applied to a value of another width");
                            }
                            Ok(s)
                        })
                        .collect::<Result<_>>()?;
                    return match (f.arity, ts.as_slice()) {
                        (1, [a]) => Ok((format!("(.fn {k} {a})"), t)),
                        (2, [a, b]) => Ok((format!("(.fn2 {k} {a} {b})"), t)),
                        _ => bail!("{head} has arity {}", f.arity),
                    };
                }
                bail!("unsupported term {s}")
            }
            Sexp::Str(_) => bail!("unexpected string"),
        }
    }

    /// The memory of a memory annotation: `old_…` and @requires read the memory at entry.
    fn mr(&self, head: &str) -> Result<&'static str> {
        if !self.memory {
            bail!("{head} needs `memory = true` (generator 2)");
        }
        Ok(if head.starts_with("old_") || self.mode == Mode::Pre {
            "(.v 0)"
        } else {
            ".cur"
        })
    }

    /// A condition used by `ite`, as an `i32` term (comparisons only).
    fn cond(&self, s: &Sexp) -> Result<String> {
        let l = s.list().context("ite condition must be a comparison")?;
        let head = l.first().and_then(Sexp::atom).unwrap_or_default();
        if let Some((_, op)) = REL.iter().find(|(n, _)| *n == head) {
            let [a, b] = &l[1..] else {
                bail!("{head} takes two arguments")
            };
            let (a, _) = self.tm(a)?;
            let (b, _) = self.tm(b)?;
            return Ok(format!("(.rel {op} {a} {b})"));
        }
        bail!("ite condition must be a comparison: {s}")
    }

    /// A formula: Lean `Fm` syntax.
    fn fm(&self, s: &Sexp) -> Result<String> {
        if let Some(a) = s.atom() {
            return match a {
                "true" => Ok(".tt".into()),
                "false" => Ok(".ff".into()),
                _ => bail!("unsupported formula {a}"),
            };
        }
        let l = s.list().context("formula")?;
        let head = l.first().and_then(Sexp::atom).context("formula head")?;
        let args = &l[1..];
        match head {
            "not" => {
                let [p] = args else {
                    bail!("not takes one argument")
                };
                Ok(format!("(.not {})", self.fm(p)?))
            }
            "and" | "or" => {
                let mut it = args.iter().rev();
                let last = it.next().context("empty and/or")?;
                let mut acc = self.fm(last)?;
                let c = if head == "and" { ".and" } else { ".or" };
                for p in it {
                    acc = format!("({c} {} {acc})", self.fm(p)?);
                }
                Ok(acc)
            }
            "=>" => {
                let [p, q] = args else {
                    bail!("=> takes two arguments")
                };
                Ok(format!("(.imp {} {})", self.fm(p)?, self.fm(q)?))
            }
            "inbounds" | "old_inbounds" => {
                // `(inbounds a n)`: `a + n` is within the memory (`n` a decimal byte count).
                let [a, n] = args else {
                    bail!("{head} takes an address and a byte count")
                };
                let (a, ta) = self.tm(a)?;
                if ta != Ty::I32 {
                    bail!("{head} takes an i32 address");
                }
                let n: u64 = n.atom().context("byte count")?.parse()?;
                Ok(format!("(.inb {} {a} {n})", self.mr(head)?))
            }
            _ => {
                if let Some((_, op)) = REL.iter().find(|(n, _)| *n == head) {
                    let [a, b] = args else {
                        bail!("{head} takes two arguments")
                    };
                    let (a, ta) = self.tm(a)?;
                    let (b, tb) = self.tm(b)?;
                    if ta != tb {
                        bail!("{head} on different widths");
                    }
                    return Ok(format!("(.rel {op} {a} {b})"));
                }
                bail!("unsupported formula {s}")
            }
        }
    }

    fn conj(&self, ps: &[Sexp]) -> Result<String> {
        if ps.is_empty() {
            return Ok(".tt".into());
        }
        let mut it = ps.iter().rev();
        let mut acc = self.fm(it.next().unwrap())?;
        for p in it {
            acc = format!("(.and {} {acc})", self.fm(p)?);
        }
        Ok(acc)
    }
}

/// The Lean `FnSpec` and `Fns` of a target.
pub fn spec_text(cfg: &Config, t: &Target) -> Result<String> {
    let tr = |mode| Tr {
        memory: cfg.memory,
        t,
        funs: &cfg.fun,
        mode,
    };
    let tys = |v: &mut dyn Iterator<Item = Ty>| {
        v.map(|t| t.lean().to_string())
            .collect::<Vec<_>>()
            .join(", ")
    };
    let n = &cfg.name;
    let mut s = String::new();
    writeln!(s, "/-- The specification functions. -/")?;
    writeln!(s, "def {n}Fns : Fns where")?;
    for (ty, arity, field) in [
        ("i32", 1, "f32"),
        ("i64", 1, "f64"),
        ("i32", 2, "g32"),
        ("i64", 2, "g64"),
    ] {
        let fs: Vec<&Fun> = cfg
            .fun
            .iter()
            .filter(|f| f.ty == ty && f.arity == arity)
            .collect();
        if fs.is_empty() {
            continue;
        }
        let args = if arity == 1 { "x" } else { "x y" };
        let mut body = "match k with".to_string();
        for (k, f) in fs.iter().enumerate() {
            write!(body, " | {k} => {} {args}", f.lean)?;
        }
        write!(body, " | _ => x")?;
        writeln!(s, "  {field} k {args} := {body}")?;
    }
    writeln!(s)?;
    writeln!(s, "/-- The annotations of `${}`. -/", cfg.func)?;
    writeln!(s, "def {n}Spec : FnSpec where")?;
    writeln!(
        s,
        "  params := [{}]",
        tys(&mut t.params.iter().map(|p| p.1))
    )?;
    writeln!(s, "  results := [{}]", tys(&mut t.results.iter().copied()))?;
    writeln!(s, "  pre := {}", tr(Mode::Pre).conj(&t.requires)?)?;
    writeln!(s, "  post := {}", tr(Mode::Post).conj(&t.ensures)?)?;
    let invs: Vec<String> = t
        .invariants
        .iter()
        .map(|i| tr(Mode::Inv).fm(i))
        .collect::<Result<_>>()?;
    writeln!(s, "  inv := [{}]", invs.join(",\n    "))?;
    if cfg.memory {
        if cfg.generator != 2 {
            bail!("`memory = true` needs `generator = 2`");
        }
        writeln!(s, "  mem := true")?;
    }
    Ok(s)
}

/// Candidate tactics for every condition (after `vcgen`), first that closes it wins.
fn candidates(cfg: &Config) -> Vec<String> {
    let mut c = cfg.tactics.clone();
    for t in [
        "decide",
        "(intros; simp_all)",
        "(intros; bv_omega)",
        "(intros; omega)",
        "(intros; split_ifs <;> simp_all)",
        "(intros; split_ifs <;> bv_omega)",
        // generator 2: the path conditions bind fresh variables (`v = term`); substitute them
        "(intros; subst_vars; simp_all)",
        "(intros; subst_vars; bv_omega)",
    ] {
        c.push(t.to_string());
    }
    c
}

pub struct Paths {
    pub dir: PathBuf,
    pub lean: PathBuf,
    pub smt: PathBuf,
}

/// Write the Lean files: the proof attempt and the SMT dump.
pub fn write(root: &Path, cfg: &Config, t: &Target, src: &str, out: &Path) -> Result<Paths> {
    std::fs::create_dir_all(out)?;
    let n = &cfg.name;
    let (module, tactic) = match cfg.generator {
        1 => ("VCGen", "vcgen"),
        2 => ("VCGen2", "vcgen2"),
        g => bail!("unknown generator {g} (1 or 2)"),
    };
    let mut head = String::new();
    writeln!(head, "import Silmaril.Wasm.Auto.{module}.Thms")?;
    let smt_module = if cfg.generator == 1 {
        "VCSmt"
    } else {
        "VCSmt2"
    };
    writeln!(head, "import Silmaril.Wasm.Auto.{smt_module}.Defs")?;
    writeln!(head, "import Silmaril.Wasm.Wat")?;
    writeln!(head, "import Mathlib.Tactic.SplitIfs")?;
    for i in &cfg.imports {
        writeln!(head, "import {i}")?;
    }
    writeln!(
        head,
        "\n/-! Generated by `tools/wasm-vc reflect` from `{}`. -/\n",
        cfg.source
    )?;
    writeln!(head, "open Silmaril.Wasm.Auto.{module}\n")?;
    writeln!(head, "set_option maxRecDepth 100000\n")?;
    if src.contains("\"#") {
        bail!("the source must not contain \"#");
    }
    writeln!(
        head,
        "def {n}Program := wat3! r#\"\n{}\"#\n",
        src.trim_end()
    )?;
    writeln!(
        head,
        "def {n}Func : Silmaril.Wasm.Func := {n}Program.funcs[{}]\n",
        t.index
    )?;
    head.push_str(&spec_text(cfg, t)?);
    let fuel = cfg.fuel;
    let smt = format!(
        "{head}\n#eval IO.println (Silmaril.Wasm.Auto.{module}.smtScript (genFunc {n}Spec {n}Func {fuel}))\n"
    );
    let cands = candidates(cfg)
        .iter()
        .map(|c| format!("    | {c}"))
        .collect::<Vec<_>>()
        .join("\n");
    let proof = format!(
        "{head}\n/-- The verification conditions of `${}`. -/\ntheorem {n}_vcs : AllValid {n}Fns (genFunc {n}Spec {n}Func {fuel}) := by\n  {tactic}\n  all_goals (try simp only [{n}Fns])\n  all_goals first\n{cands}\n",
        cfg.func
    );
    let _ = root;
    let paths = Paths {
        dir: out.to_path_buf(),
        lean: out.join(format!("{n}.lean")),
        smt: out.join(format!("{n}Smt.lean")),
    };
    std::fs::write(&paths.lean, proof)?;
    std::fs::write(&paths.smt, smt)?;
    Ok(paths)
}

/// One z3 verdict.
pub struct Verdict {
    pub index: usize,
    pub uses_fns: bool,
    pub status: String,
    pub model: String,
    pub seconds: f64,
}

/// Split the SMT dump and run z3 on each query.
pub fn smt(dump: &str, dir: &Path, timeout_s: u32) -> Result<Vec<Verdict>> {
    let mut out = Vec::new();
    let mut chunks: Vec<(usize, bool, String)> = Vec::new();
    for line in dump.lines() {
        if let Some(rest) = line.strip_prefix(";; vc ") {
            let mut it = rest.split_whitespace();
            let k: usize = it.next().context("vc index")?.parse()?;
            let uf = it.next() == Some("uf");
            chunks.push((k, uf, String::new()));
        } else if let Some(c) = chunks.last_mut() {
            c.2.push_str(line);
            c.2.push('\n');
        }
    }
    for (k, uf, q) in chunks {
        let f = dir.join(format!("vc{k}.smt2"));
        std::fs::write(&f, &q)?;
        let start = Instant::now();
        let o = Command::new("z3")
            .arg(format!("-T:{timeout_s}"))
            .arg(&f)
            .output()
            .context("could not run z3")?;
        let text = String::from_utf8_lossy(&o.stdout).to_string();
        let status = text.lines().next().unwrap_or("error").trim().to_string();
        let model = if status == "sat" {
            text.lines().skip(1).collect::<Vec<_>>().join("\n")
        } else {
            String::new()
        };
        out.push(Verdict {
            index: k,
            uses_fns: uf,
            status,
            model,
            seconds: start.elapsed().as_secs_f64(),
        });
    }
    Ok(out)
}

/// The `reflect` subcommand.
pub fn run(config: &Path, out: Option<PathBuf>, use_smt: bool) -> Result<()> {
    let config = std::fs::canonicalize(config)?;
    let base = config.parent().context("configuration directory")?;
    let root = crate::lake_root(base)?;
    let cfg: Config =
        toml::from_str(&std::fs::read_to_string(&config)?).context("invalid reflect.toml")?;
    let src = std::fs::read_to_string(base.join(&cfg.source))?;
    let t = target(&src, &cfg.func)?;
    let out = out.unwrap_or_else(|| root.join("target/wasm-vc/reflect").join(&cfg.name));
    let p = write(&root, &cfg, &t, &src, &out)?;
    println!("wrote {} and {}", p.lean.display(), p.smt.display());
    let lean = |f: &Path| -> Result<(bool, String, f64)> {
        let start = Instant::now();
        let o = Command::new("lake")
            .args(["env", "lean"])
            .arg(f)
            .current_dir(&root)
            .output()
            .context("could not run lake")?;
        let mut text = String::from_utf8_lossy(&o.stdout).to_string();
        text.push_str(&String::from_utf8_lossy(&o.stderr));
        Ok((o.status.success(), text, start.elapsed().as_secs_f64()))
    };
    if use_smt && crate::smt::available("z3") {
        let (ok, dump, secs) = lean(&p.smt)?;
        if !ok {
            bail!("computing the conditions failed:\n{dump}");
        }
        println!("conditions computed by Lean in {secs:.1}s");
        for v in smt(&dump, &p.dir, 60)? {
            println!(
                "vc {}: z3 {} ({:.2}s){}",
                v.index,
                v.status,
                v.seconds,
                if v.uses_fns {
                    ", uses uninterpreted symbols"
                } else {
                    ""
                }
            );
            if v.status == "sat" {
                println!(
                    "  {} counterexample:\n{}",
                    if v.uses_fns {
                        "possible (uninterpreted symbols or memory equality)"
                    } else {
                        "genuine"
                    },
                    v.model
                );
            }
        }
    } else if use_smt {
        println!("z3 not found: SMT check skipped");
    }
    let (ok, text, secs) = lean(&p.lean)?;
    if ok {
        println!("proved: every condition closed by a candidate tactic ({secs:.1}s)");
    } else {
        println!("not proved ({secs:.1}s); Lean output:\n{text}");
        std::process::exit(2);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    const SRC: &str = "(module
  ;; @requires (bvult x #x0000000000000064)
  ;; @ensures (= result (bvadd x #x0000000000000001))
  (func $inc (param $x i64) (result i64) (local $y i32)
    ;; @invariant (bvule (old x) #x0000000000000064)
    (i64.add (local.get $x) (i64.const 1))))";

    #[test]
    fn reads_and_translates_annotations() {
        let t = target(SRC, "inc").unwrap();
        assert_eq!(t.params, vec![(Some("x".into()), Ty::I64)]);
        assert_eq!(t.locals, vec![(Some("y".into()), Ty::I32)]);
        assert_eq!(t.results, vec![Ty::I64]);
        let cfg = Config {
            name: "inc".into(),
            source: "inc.wat".into(),
            func: "inc".into(),
            fuel: 10,
            imports: vec![],
            fun: vec![],
            tactics: vec![],
            generator: 1,
            memory: false,
        };
        let s = spec_text(&cfg, &t).unwrap();
        assert!(
            s.contains("pre := (.rel (.lt .unsigned) (.var .i64 0) (.lit .i64 100))"),
            "{s}"
        );
        assert!(
            s.contains("post := (.rel .eq (.loc .i64 0) (.bin .add (.var .i64 0) (.lit .i64 1)))"),
            "{s}"
        );
        assert!(
            s.contains("inv := [(.rel (.le .unsigned) (.var .i64 0) (.lit .i64 100))]"),
            "{s}"
        );
    }
}
