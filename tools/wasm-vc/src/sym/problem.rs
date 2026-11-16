//! Wasm problems (`*.toml`) and their solving: functional equivalence of two
//! programs (`equiv`), a function against a reference relation in SMT-LIB
//! (`post`), and bounded checks of call/trap/state properties over runs
//! (`bmc`). The format and the verdicts are documented in `docs/wasm-solvers.md`.

use super::exec::{Event, HostModel, Limits, Machine, Outcome, State};
use super::module::Module;
use super::solve::{self, Answer, F, Query, Status};
use super::term::{Bv2, Id, Rel, Sort};
use anyhow::{Context, Result, bail};
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};
use std::time::Instant;

#[derive(Debug, Deserialize, Clone)]
#[serde(deny_unknown_fields)]
pub struct ModSpec {
    /// Instance name; later modules importing from this name are linked to it.
    pub name: String,
    /// `.wat` or `.wasm` file, relative to the problem file.
    pub wat: String,
}

#[derive(Debug, Deserialize, Clone)]
#[serde(deny_unknown_fields)]
/// One step of a call sequence (`calls = [{ func, args, repeat }]`).
pub struct CallStep {
    /// Function (export name, `$name` or index) of the main instance, or `inst:func`.
    pub func: String,
    /// Arguments: SMT-LIB literals or names of problem parameters.
    #[serde(default)]
    pub args: Vec<String>,
    #[serde(default = "one")]
    pub repeat: u32,
}

fn one() -> u32 {
    1
}

#[derive(Debug, Deserialize, Clone)]
#[serde(deny_unknown_fields)]
pub struct Side {
    pub modules: Vec<ModSpec>,
    /// Entry function of the last module (shortcut for one call).
    #[serde(default)]
    pub entry: Option<String>,
    #[serde(default)]
    pub calls: Vec<CallStep>,
    /// With a symbolic initial state: byte ranges `mK:OFF:N` of the main
    /// instance's memories that keep their module-initialised contents
    /// (tables of the simulator, as opposed to its state).
    #[serde(default)]
    pub keep: Vec<String>,
}

#[derive(Debug, Deserialize, Clone)]
#[serde(deny_unknown_fields)]
pub struct MapEntry {
    #[serde(default)]
    pub name: Option<String>,
    pub a: String,
    pub b: String,
}

#[derive(Debug, Deserialize, Clone)]
#[serde(deny_unknown_fields)]
pub struct FrameSpec {
    pub mem: String,
    pub except: Vec<String>,
}

/// A callee contract (assume-guarantee), see `exec::Contract`.
#[derive(Debug, Deserialize, Clone)]
#[serde(deny_unknown_fields)]
pub struct ContractSpec {
    /// `module.name` of the import.
    pub import: String,
    pub name: String,
    #[serde(default = "tru")]
    pub pre: String,
    pub post: String,
    /// `values` or `x86`.
    pub style: String,
    #[serde(default)]
    pub params: Vec<String>,
    #[serde(default)]
    pub results: Vec<String>,
}

fn tru() -> String {
    "true".into()
}

/// A loop annotation: loop `loop` (pre-order) of function `func`.
#[derive(Debug, Deserialize, Clone)]
#[serde(deny_unknown_fields)]
pub struct LoopAnn {
    pub func: String,
    pub r#loop: u32,
    pub invariant: String,
    #[serde(default)]
    pub decreases: Option<String>,
    #[serde(default)]
    pub parts: Vec<String>,
    #[serde(default)]
    pub measures: Vec<String>,
}

#[derive(Debug, Deserialize, Clone)]
#[serde(deny_unknown_fields)]
pub struct NeverCall {
    /// `module.name` of the import (a trailing `*` matches a prefix).
    pub import: String,
    /// SMT-LIB condition under which the call is allowed (over `arg0`…, state names).
    #[serde(default)]
    pub unless: Option<String>,
}

#[derive(Debug, Deserialize, Clone, Default)]
#[serde(deny_unknown_fields)]
pub struct EnvSpec {
    /// `opaque` (default): `mem.*` imports are opaque; `array`: they access one
    /// environment memory (a byte array, initially arbitrary or `data`).
    #[serde(default)]
    pub mem: Option<String>,
    #[serde(default)]
    pub data: Vec<DataSpec>,
}

#[derive(Debug, Deserialize, Clone)]
#[serde(deny_unknown_fields)]
pub struct DataSpec {
    pub addr: String,
    #[serde(default)]
    pub file: Option<String>,
    #[serde(default)]
    pub hex: Option<String>,
}

#[derive(Debug, Deserialize, Clone)]
#[serde(deny_unknown_fields)]
pub struct Param {
    pub name: String,
    /// `i32` or `i64` (or `bvN`).
    pub ty: String,
}

#[derive(Debug, Deserialize, Clone)]
#[serde(deny_unknown_fields)]
pub struct Problem {
    /// Format version, optional: `wasm-vc.problem.v1` (the only version so far).
    #[serde(default)]
    pub schema: Option<String>,
    #[serde(default)]
    pub name: Option<String>,
    pub kind: String,
    /// Free-text documentation in problem files; not used by the checker, but declared so
    /// that `deny_unknown_fields` accepts it.
    #[serde(default)]
    #[allow(dead_code)]
    pub description: Option<String>,
    /// Problems this one depends on (names), for drivers; informational here.
    #[serde(default)]
    pub deps: Vec<String>,
    #[serde(default)]
    pub a: Option<Side>,
    #[serde(default)]
    pub b: Option<Side>,
    /// Shorthand for a single side `a`.
    #[serde(default)]
    pub modules: Vec<ModSpec>,
    #[serde(default)]
    pub entry: Option<String>,
    #[serde(default)]
    pub calls: Vec<CallStep>,
    /// Free parameters (default: the entry's parameters `p0`, `p1`, …).
    #[serde(default)]
    pub params: Vec<Param>,
    /// `symbolic` (default for equiv/post): arbitrary initial globals and memories;
    /// `module`: the module's initial values.
    #[serde(default)]
    pub init: Option<String>,
    #[serde(default)]
    pub pre: Vec<String>,
    #[serde(default)]
    pub post: Vec<String>,
    #[serde(default)]
    pub map: Vec<MapEntry>,
    /// equiv: observations of side `b` that the call must leave unchanged.
    #[serde(default)]
    pub unchanged_b: Vec<String>,
    /// equiv: memory `mK` of side `b` is unchanged outside the byte ranges `OFF:N`.
    #[serde(default)]
    pub frame_b: Option<FrameSpec>,
    /// A TOML file with further `[[map]]` entries (relative to the problem).
    #[serde(default)]
    pub map_from: Option<String>,
    /// equiv: what to compare (`result`, `trap`, `hist`, `map`, `globals`, `memory`).
    #[serde(default)]
    pub observe: Vec<String>,
    #[serde(default)]
    pub never_call: Vec<NeverCall>,
    /// Callee contracts replacing imports.
    #[serde(default)]
    pub contracts: Vec<ContractSpec>,
    /// The memory `(memN a)` in formulas reads: `env` (the environment memory)
    /// or an imported memory `module.name`; bound as `|mem!old|`/`|mem!post|`.
    #[serde(default)]
    pub mem_obs: Option<String>,
    /// SMT-LIB definitions (`define-fun`, `define-fun-rec`, `declare-fun`) used by formulas.
    #[serde(default)]
    pub defines: Vec<String>,
    /// Loop invariants (cut loops instead of unrolling them).
    #[serde(default)]
    pub loops: Vec<LoopAnn>,
    /// Case split: parameter name to its values (list, or `"lo..hi"`).
    #[serde(default)]
    pub cases: std::collections::BTreeMap<String, toml::Value>,
    /// Finite domains of parameters (list, or `"lo..hi"`): the parameter is
    /// assumed in its domain and represented as an `ite` over the values, so
    /// that table lookups and dispatch on it distribute into literal cases
    /// inside one symbolic execution (cheaper than `cases`).
    #[serde(default)]
    pub domains: std::collections::BTreeMap<String, toml::Value>,
    /// Infer invariants for unannotated loops of the entry (default true).
    #[serde(default)]
    pub infer: Option<bool>,
    /// Check the conjunction of all goals first (default true).
    #[serde(default)]
    pub batch: Option<bool>,
    #[serde(default)]
    pub no_trap: bool,
    #[serde(default)]
    pub env: EnvSpec,
    #[serde(default)]
    pub unroll: Option<u32>,
    #[serde(default)]
    pub depth: Option<u32>,
    #[serde(default)]
    pub solver: Option<String>,
    #[serde(default)]
    pub timeout: Option<u64>,
    /// Expected verdict (for regression tests): proved | refuted | bounded.
    #[serde(default)]
    pub expect: Option<String>,
}

#[derive(Debug, Serialize, Clone)]
pub struct Report {
    pub problem: String,
    pub kind: String,
    /// proved | partial | refuted | bounded | unknown | error (docs/wasm-solvers.md)
    pub verdict: String,
    /// How the verdict is justified.
    pub trust: String,
    pub seconds: f64,
    pub symex_seconds: f64,
    pub symex_steps: u64,
    pub terms: usize,
    pub goals: Vec<Answer>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub expect: Option<String>,
    #[serde(skip_serializing_if = "String::is_empty")]
    pub error: String,
}

pub struct Opts {
    pub solver: Option<String>,
    pub timeout: Option<u64>,
    pub work: PathBuf,
    /// Override of the problem's loop unrolling bound.
    pub unroll: Option<u32>,
}

fn parse_lit(s: &str) -> Option<(u64, Option<u32>)> {
    let s = s.trim();
    if let Some(h) = s.strip_prefix("#x") {
        return u64::from_str_radix(h, 16)
            .ok()
            .map(|v| (v, Some(4 * h.len() as u32)));
    }
    if let Some(b) = s.strip_prefix("#b") {
        return u64::from_str_radix(b, 2)
            .ok()
            .map(|v| (v, Some(b.len() as u32)));
    }
    if let Some(h) = s.strip_prefix("0x") {
        return u64::from_str_radix(&h.replace('_', ""), 16)
            .ok()
            .map(|v| (v, None));
    }
    if let Some(n) = s.strip_prefix('-') {
        return n.parse::<u64>().ok().map(|v| (v.wrapping_neg(), None));
    }
    s.replace('_', "").parse::<u64>().ok().map(|v| (v, None))
}

/// One side of a problem, instantiated in the shared machine.
struct Inst {
    tag: String,
    main: usize,
    insts: Vec<usize>,
}

/// An observation: a location of a side's state, or its result.
#[derive(Clone, Debug)]
enum Obs {
    Global(usize),
    Mem {
        slot: usize,
        off: u64,
        n: u32,
    },
    Result(usize),
    /// Bits `hi..=lo` of another observation.
    Slice(Box<Obs>, u32, u32),
}

struct Ctx {
    m: Machine,
    dir: PathBuf,
}

impl Ctx {
    fn side(&mut self, tag: &str, side: &Side, env: &EnvSpec) -> Result<Inst> {
        self.side_c(tag, side, env, &[])
    }

    fn side_c(
        &mut self,
        tag: &str,
        side: &Side,
        env: &EnvSpec,
        cs: &[ContractSpec],
    ) -> Result<Inst> {
        let mut insts = Vec::new();
        let env_array = env.mem.as_deref() == Some("array");
        let mut cmap: Vec<(String, usize)> = Vec::new();
        for c in cs {
            cmap.push((c.import.clone(), self.m.contracts.len()));
            self.m.contracts.push(super::exec::Contract {
                name: c.name.clone(),
                pre: c.pre.clone(),
                post: c.post.clone(),
                style: if c.style == "x86" {
                    super::exec::ContractStyle::X86 {
                        regs: vec![],
                        mem: None,
                    }
                } else {
                    super::exec::ContractStyle::Values {
                        params: c.params.clone(),
                        results: c.results.clone(),
                    }
                },
            });
        }
        for ms in &side.modules {
            let path = self.dir.join(&ms.wat);
            let module = Module::load(&path)?;
            let cmap = cmap.clone();
            let model = move |md: &str, nm: &str| -> HostModel {
                let key = format!("{md}.{nm}");
                if let Some((_, k)) = cmap.iter().find(|c| c.0 == key) {
                    return HostModel::Contract(*k);
                }
                if env_array && md == "mem" {
                    let n = |s: &str| nm.strip_prefix(s).and_then(|r| r.parse::<u32>().ok());
                    if let Some(b) = n("load") {
                        return HostModel::EnvLoad(b / 8);
                    }
                    if let Some(b) = n("store") {
                        return HostModel::EnvStore(b / 8);
                    }
                }
                HostModel::Opaque
            };
            let name = format!("{tag}{}", ms.name);
            let k = self.m.instantiate_scoped(&name, tag, module, &model)?;
            insts.push(k);
        }
        let main = *insts.last().context("a side needs modules")?;
        // x86 contracts: the simulator's register slots and the memory
        for (_, k) in &cmap {
            if let super::exec::ContractStyle::X86 { regs, mem } = &mut self.m.contracts[*k].style {
                for (r, g) in super::annot::X86_REGS {
                    for &i in insts.iter().rev() {
                        if let Ok(gi) = self.m.insts[i].m.find_global(g) {
                            regs.push((
                                r.to_string(),
                                self.m.insts[i].globals[gi as usize],
                                super::annot::is_flag(r),
                            ));
                            break;
                        }
                    }
                }
                *mem = self
                    .m
                    .env_mem
                    .or_else(|| self.m.mem_imports.values().next().copied());
            }
        }
        Ok(Inst {
            tag: tag.to_string(),
            main,
            insts,
        })
    }

    fn find_func(&self, s: &Inst, f: &str) -> Result<(usize, u32)> {
        if let Some((i, g)) = f.split_once(':') {
            let k = s
                .insts
                .iter()
                .copied()
                .find(|&k| self.m.insts[k].name == format!("{}{i}", s.tag))
                .with_context(|| format!("no instance {i}"))?;
            return Ok((k, self.m.insts[k].m.find_func(g)?));
        }
        Ok((s.main, self.m.insts[s.main].m.find_func(f)?))
    }

    fn global_slot(&self, s: &Inst, name: &str) -> Result<usize> {
        for &k in s.insts.iter().rev() {
            if let Ok(g) = self.m.insts[k].m.find_global(name) {
                return Ok(self.m.insts[k].globals[g as usize]);
            }
        }
        bail!("no global {name}")
    }

    /// `g:NAME`, `m:OFF:N`, `mK:OFF:N`, `env:OFF:N`, `result`, `result:K`, each
    /// optionally followed by a bit slice `@BIT` or `@HI-LO`.
    fn obs(&self, s: &Inst, spec: &str) -> Result<Obs> {
        if let Some((base, sl)) = spec.rsplit_once('@') {
            let o = self.obs(s, base)?;
            let (hi, lo) = match sl.split_once('-') {
                Some((h, l)) => (h.parse()?, l.parse()?),
                None => (sl.parse()?, sl.parse()?),
            };
            return Ok(Obs::Slice(Box::new(o), hi, lo));
        }
        let parts: Vec<&str> = spec.split(':').collect();
        match parts.as_slice() {
            ["g", n] => Ok(Obs::Global(self.global_slot(s, n)?)),
            ["result"] => Ok(Obs::Result(0)),
            ["result", k] => Ok(Obs::Result(k.parse()?)),
            [m, off, n] => {
                let slot = if *m == "env" {
                    self.m
                        .env_mem
                        .context("no environment memory (env.mem = \"array\")")?
                } else {
                    let k: usize = m
                        .strip_prefix('m')
                        .context("observation")?
                        .parse()
                        .unwrap_or(0);
                    self.m.insts[s.main].mems[k]
                };
                let off = parse_lit(off).context("offset")?.0;
                Ok(Obs::Mem {
                    slot,
                    off,
                    n: n.parse()?,
                })
            }
            _ => bail!("bad observation {spec}"),
        }
    }

    fn read(&mut self, o: &Obs, st: &State, results: &[Id]) -> Result<Id> {
        Ok(match o {
            Obs::Global(g) => st.g[*g],
            Obs::Result(k) => *results.get(*k).context("no such result")?,
            Obs::Mem { slot, off, n } => {
                let aw = match self.m.t.sort(st.m[*slot]) {
                    Sort::Mem(aw) => aw,
                    _ => unreachable!(),
                };
                let a = self.m.t.lit(*off, aw);
                self.m.t.load_le(st.m[*slot], a, *n)
            }
            Obs::Slice(o, hi, lo) => {
                let v = self.read(o, st, results)?;
                self.m.t.extract(*hi, *lo, v)
            }
        })
    }

    /// Equality of two values, zero-extending the narrower.
    fn eq_ext(&mut self, x: Id, y: Id) -> Id {
        // whole memories (array sort): plain equality (elf-verify: `observe = ["memory"]`)
        if matches!(self.m.t.sort(x), Sort::Mem(_)) || matches!(self.m.t.sort(y), Sort::Mem(_)) {
            return self.m.t.eq(x, y);
        }
        let (wx, wy) = (self.m.t.width(x), self.m.t.width(y));
        let x = if wx < wy {
            self.m.t.zext(wy - wx, x)
        } else {
            x
        };
        let y = if wy < wx {
            self.m.t.zext(wx - wy, y)
        } else {
            y
        };
        self.m.t.eq(x, y)
    }

    /// Run the calls of a side from `st`.
    fn run(
        &mut self,
        s: &Inst,
        side: &Side,
        params: &[(String, Id)],
        st: State,
    ) -> Result<(Outcome, Id)> {
        let mut calls = side.calls.clone();
        if let Some(e) = &side.entry {
            calls.insert(
                0,
                CallStep {
                    func: e.clone(),
                    args: vec![],
                    repeat: 1,
                },
            );
        }
        if calls.is_empty() {
            bail!("side {} has no entry or calls", s.tag);
        }
        let mut guard = self.m.t.tt();
        let mut st = st;
        let mut results = Vec::new();
        let n_calls = calls.len();
        for (ci, c) in calls.iter().enumerate() {
            let (k, f) = self.find_func(s, &c.func)?;
            let ty = self.m.insts[k].m.func_ty(f).clone();
            let args: Vec<Id> = if c.args.is_empty() && ci == 0 && n_calls == 1 {
                // the entry's parameters are the problem parameters
                if params.len() != ty.params.len() {
                    bail!(
                        "{} takes {} parameters, the problem has {}",
                        c.func,
                        ty.params.len(),
                        params.len()
                    );
                }
                params.iter().map(|p| p.1).collect()
            } else {
                c.args
                    .iter()
                    .zip(&ty.params)
                    .map(|(a, t)| {
                        if let Some((v, _)) = parse_lit(a) {
                            Ok(self.m.t.lit(v, t.width()))
                        } else {
                            params
                                .iter()
                                .find(|p| p.0 == *a)
                                .map(|p| p.1)
                                .with_context(|| format!("unknown argument {a}"))
                        }
                    })
                    .collect::<Result<_>>()?
            };
            for _ in 0..c.repeat {
                let o = self.m.call(k, f, args.clone(), guard, st)?;
                guard = o.guard;
                st = o.st;
                results = o.results;
            }
        }
        let traps = self.m.traps.iter().map(|x| x.0).collect::<Vec<_>>();
        let trap = self.m.t.or(&traps);
        Ok((Outcome { guard, st, results }, trap))
    }

    /// Names for user formulas: parameters, globals (`P.g.NAME` initial,
    /// `P.post.g.NAME` final), results (`P.result`, `P.resultK`), map entries.
    fn binds(&self, s: &Inst, pre: &State, post: Option<&Outcome>) -> Vec<(String, Id)> {
        let mut b = Vec::new();
        let p = if s.tag.is_empty() {
            String::new()
        } else {
            s.tag.clone()
        };
        for &k in &s.insts {
            let inst = &self.m.insts[k];
            for (gi, &slot) in inst.globals.iter().enumerate() {
                let n = inst.m.global_name(gi as u32);
                b.push((format!("{p}g.{n}"), pre.g[slot]));
                if let Some(o) = post {
                    b.push((format!("{p}post.g.{n}"), o.st.g[slot]));
                }
            }
        }
        if let Some(o) = post {
            for (i, &r) in o.results.iter().enumerate() {
                b.push((format!("{p}result{i}"), r));
                if i == 0 {
                    b.push((format!("{p}result"), r));
                }
            }
        }
        // de-duplicate names (later instances shadow earlier ones)
        let mut seen = std::collections::HashSet::new();
        b.reverse();
        b.retain(|(n, _)| seen.insert(n.clone()));
        b.reverse();
        b
    }
}

impl Machine {
    /// `instantiate` with imports linked inside one side (`scope` prefix).
    pub fn instantiate_scoped(
        &mut self,
        name: &str,
        scope: &str,
        m: Module,
        model: &dyn Fn(&str, &str) -> HostModel,
    ) -> Result<usize> {
        // rename imports' modules into the scope for linking
        let mut m = m;
        for imp in &mut m.imports {
            let scoped = format!("{scope}{}", imp.module);
            if self.insts.iter().any(|i| i.name == scoped) {
                imp.module = scoped;
            }
        }
        for g in &mut m.globals {
            if g.init.is_none()
                && let Some(n) = &g.name
                && let Some((md, rest)) = n.split_once('.')
            {
                let scoped = format!("{scope}{md}");
                if self.insts.iter().any(|i| i.name == scoped) {
                    g.name = Some(format!("{scoped}.{rest}"));
                }
            }
        }
        self.instantiate(name, m, model)
    }
}

fn param_sort(ty: &str) -> Result<u32> {
    Ok(match ty {
        "i32" => 32,
        "i64" => 64,
        t => t
            .strip_prefix("bv")
            .and_then(|n| n.parse().ok())
            .with_context(|| format!("bad parameter type {t}"))?,
    })
}

/// The problem format version this build reads (`schema = "..."`, optional in problem files).
pub const SCHEMA: &str = "wasm-vc.problem.v1";

pub fn load(path: &Path) -> Result<Problem> {
    if path.extension().is_some_and(|e| e == "wat") {
        return super::annot::problem_of_wat(path);
    }
    let text =
        std::fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))?;
    let mut p: Problem =
        toml::from_str(&text).with_context(|| format!("parsing {}", path.display()))?;
    if p.name.is_none() {
        p.name = path.file_stem().map(|s| s.to_string_lossy().to_string());
    }
    if let Some(s) = &p.schema
        && s != SCHEMA
    {
        eprintln!(
            "warning: {}: unknown schema {s:?} (this wasm-vc reads {SCHEMA:?}); continuing",
            path.display()
        );
    }
    Ok(p)
}

pub fn solve_file(path: &Path, opts: &Opts) -> Report {
    let start = Instant::now();
    let name = path
        .file_stem()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_default();
    // a work directory per problem file (parent directory and stem)
    let tag = format!(
        "{}_{}",
        path.parent()
            .and_then(|d| d.file_name())
            .map(|s| s.to_string_lossy().to_string())
            .unwrap_or_default(),
        name
    );
    let opts = &Opts {
        solver: opts.solver.clone(),
        timeout: opts.timeout,
        work: opts.work.join(tag),
        unroll: opts.unroll,
    };
    match load(path).and_then(|p| solve(&p, path.parent().unwrap_or(Path::new(".")), opts)) {
        Ok(r) => r,
        Err(e) => Report {
            problem: name,
            kind: String::new(),
            verdict: "error".into(),
            trust: String::new(),
            seconds: start.elapsed().as_secs_f64(),
            symex_seconds: 0.0,
            symex_steps: 0,
            terms: 0,
            goals: vec![],
            expect: None,
            error: format!("{e:#}"),
        },
    }
}

/// Values of a case-split parameter: a list of literals or a range `"lo..hi"` (inclusive).
fn case_values(v: &toml::Value) -> Result<Vec<u64>> {
    match v {
        toml::Value::Array(a) => a
            .iter()
            .map(|x| match x {
                toml::Value::Integer(i) => Ok(*i as u64),
                toml::Value::String(s) => parse_lit(s).map(|x| x.0).context("case value"),
                _ => bail!("case values are integers or strings"),
            })
            .collect(),
        toml::Value::String(s) => {
            let (lo, hi) = s.split_once("..").context("ranges are \"lo..hi\"")?;
            let lo = parse_lit(lo).context("range")?.0;
            let hi = parse_lit(hi).context("range")?.0;
            Ok((lo..=hi).collect())
        }
        _ => bail!("cases: list or \"lo..hi\""),
    }
}

/// Solve a problem; with `cases`, once per combination of the listed
/// parameters' values (each a separate symbolic execution with the
/// parameters fixed, so that dispatch on them folds away).
pub fn solve(p: &Problem, dir: &Path, opts: &Opts) -> Result<Report> {
    if p.infer.unwrap_or(true)
        && let Some(inf) = super::infer::infer(p, dir, opts)?
    {
        let mut q = p.clone();
        q.loops.extend(inf.loops);
        q.infer = Some(false);
        let mut r = solve(&q, dir, opts)?;
        r.trust = format!(
            "{}; inferred ({} Houdini rounds): {}",
            r.trust,
            inf.rounds,
            inf.note.trim()
        );
        return Ok(r);
    }
    if p.cases.is_empty() {
        return solve_case(p, dir, opts, &[]);
    }
    let start = Instant::now();
    let mut combos: Vec<Vec<(String, u64)>> = vec![vec![]];
    for (n, v) in &p.cases {
        let vals = case_values(v)?;
        combos = combos
            .into_iter()
            .flat_map(|c| {
                vals.iter().map(move |&x| {
                    let mut c = c.clone();
                    c.push((n.clone(), x));
                    c
                })
            })
            .collect();
    }
    let mut goals = Vec::new();
    let (mut symex, mut steps, mut terms) = (0.0, 0, 0);
    let mut verdicts = Vec::new();
    let mut trust = String::new();
    for c in &combos {
        let r = solve_case(p, dir, opts, c)?;
        let tag: Vec<String> = c.iter().map(|(n, v)| format!("{n}={v}")).collect();
        let tag = tag.join(",");
        symex += r.symex_seconds;
        steps += r.symex_steps;
        terms = terms.max(r.terms);
        if r.verdict != "proved" {
            for mut g in r.goals {
                g.name = format!("[{tag}] {}", g.name);
                goals.push(g);
            }
        } else {
            let secs: f64 = r.goals.iter().map(|g| g.seconds).sum();
            let nodes = r.goals.iter().map(|g| g.nodes).max().unwrap_or(0);
            goals.push(Answer {
                name: format!("[{tag}]"),
                status: Status::Proved,
                solver: r
                    .goals
                    .first()
                    .map(|g| g.solver.clone())
                    .unwrap_or_default(),
                seconds: secs,
                model: vec![],
                note: String::new(),
                nodes,
                bytes: 0,
            });
        }
        if trust.is_empty() || r.verdict != "proved" {
            trust = r.trust.clone();
        }
        verdicts.push(r.verdict);
    }
    let verdict = if verdicts.iter().any(|v| v == "refuted") {
        "refuted"
    } else if verdicts.iter().all(|v| v == "proved") {
        "proved"
    } else if verdicts.iter().all(|v| v == "proved" || v == "bounded") {
        "bounded"
    } else {
        "unknown"
    };
    Ok(Report {
        problem: p.name.clone().unwrap_or_default(),
        kind: p.kind.clone(),
        verdict: verdict.into(),
        trust: format!("{trust}; {} cases", combos.len()),
        seconds: start.elapsed().as_secs_f64(),
        symex_seconds: symex,
        symex_steps: steps,
        terms,
        goals,
        expect: p.expect.clone(),
        error: String::new(),
    })
}

fn solve_case(p: &Problem, dir: &Path, opts: &Opts, fixed: &[(String, u64)]) -> Result<Report> {
    let start = Instant::now();
    let lim = Limits {
        unroll: opts.unroll.or(p.unroll).unwrap_or(4),
        depth: p.depth.unwrap_or(32),
        hist: p.kind == "equiv",
    };
    let mut cx = Ctx {
        m: Machine::new(lim),
        dir: dir.to_path_buf(),
    };
    let solver = opts
        .solver
        .clone()
        .or(p.solver.clone())
        .unwrap_or_else(|| "z3".into());
    let timeout = opts.timeout.or(p.timeout).unwrap_or(60);
    let pname = p.name.clone().unwrap_or_default();
    let work = opts.work.clone();
    let side_a = match &p.a {
        Some(s) => s.clone(),
        None => Side {
            modules: p.modules.clone(),
            entry: p.entry.clone(),
            calls: p.calls.clone(),
            keep: vec![],
        },
    };
    let symbolic = match p.init.as_deref() {
        None => p.kind != "bmc",
        Some("symbolic") => true,
        Some("module") => false,
        Some(o) => bail!("init must be symbolic or module, not {o}"),
    };
    let mut queries: Vec<Query> = Vec::new();
    let mut mem_prelude = String::new();
    let mut base_show: Vec<(String, Id)> = Vec::new();
    let mut assume: Vec<F> = Vec::new();
    let mut complete_goal: Vec<Id> = Vec::new();
    match p.kind.as_str() {
        "equiv" => {
            let side_b = p.b.clone().context("equiv needs [a] and [b]")?;
            let a = cx.side("a.", &side_a, &p.env)?;
            let b = cx.side("b.", &side_b, &p.env)?;
            add_loops(&mut cx, &a, &p.loops)?;
            add_loops(&mut cx, &b, &p.loops)?;
            let mut st0 = cx.m.initial(symbolic, "");
            env_data(&mut cx, &p.env, dir, &mut st0)?;
            let params = make_params(&mut cx, p, &a, &side_a, fixed)?;
            assume.extend(domain_assumptions(&mut cx, p, &params)?);
            let mut p_map = p.map.clone();
            if let Some(f) = &p.map_from {
                #[derive(Deserialize)]
                struct M {
                    map: Vec<MapEntry>,
                }
                let t = std::fs::read_to_string(dir.join(f))?;
                let m: M = toml::from_str(&t).with_context(|| format!("parsing {f}"))?;
                p_map.extend(m.map);
            }
            let p = &Problem {
                map: p_map,
                ..p.clone()
            };
            // map: default identity on globals of the same name in the main instances
            let mut map: Vec<(String, Obs, Obs)> = Vec::new();
            for e in &p.map {
                let n = e.name.clone().unwrap_or_else(|| format!("{}~{}", e.a, e.b));
                map.push((n, cx.obs(&a, &e.a)?, cx.obs(&b, &e.b)?));
            }
            let observe: Vec<String> = if p.observe.is_empty() {
                ["result", "trap", "hist", "map"]
                    .iter()
                    .map(|s| s.to_string())
                    .collect()
            } else {
                p.observe.clone()
            };
            if p.map.is_empty() || observe.iter().any(|o| o == "globals") {
                let ia = &cx.m.insts[a.main];
                let ib = &cx.m.insts[b.main];
                for (gi, &sa) in ia.globals.iter().enumerate() {
                    let n = ia.m.global_name(gi as u32);
                    if let Ok(gb) = ib.m.find_global(&n) {
                        let sb = ib.globals[gb as usize];
                        if sa != sb && ia.m.globals[gi].mutable {
                            map.push((format!("g.{n}"), Obs::Global(sa), Obs::Global(sb)));
                        }
                    }
                }
            }
            if p.map.is_empty() || observe.iter().any(|o| o == "memory") {
                let (ma, mb) = (
                    cx.m.insts[a.main].mems.clone(),
                    cx.m.insts[b.main].mems.clone(),
                );
                for (k, (&sa, &sb)) in ma.iter().zip(&mb).enumerate() {
                    map.push((
                        format!("mem{k}"),
                        Obs::Global(usize::MAX - sa),
                        Obs::Global(usize::MAX - sb),
                    ));
                }
            }
            // Mapped whole globals/memories agree initially: with a symbolic initial state,
            // give both sides the same initial term (without loss of generality, also with
            // `keep`: a position kept by one side only is overwritten there), so that the
            // equalities below are syntactic and the solver need not reason about two arrays.
            if symbolic {
                for (_, oa, ob) in &map {
                    if let (Obs::Global(x), Obs::Global(y)) = (oa, ob) {
                        let (x, y) = (*x, *y);
                        match (x > usize::MAX / 2, y > usize::MAX / 2) {
                            (true, true) => {
                                let (mx, my) = (usize::MAX - x, usize::MAX - y);
                                if cx.m.t.sort(st0.m[mx]) == cx.m.t.sort(st0.m[my]) {
                                    st0.m[my] = st0.m[mx];
                                }
                            }
                            (false, false) if cx.m.t.sort(st0.g[x]) == cx.m.t.sort(st0.g[y]) => {
                                st0.g[y] = st0.g[x];
                            }
                            _ => {}
                        }
                    }
                }
                keep(&mut cx, &a, &side_a, &mut st0)?;
                keep(&mut cx, &b, &side_b, &mut st0)?;
            }
            // pre: the mapped locations agree initially
            let mut pre_eqs = Vec::new();
            for (_, oa, ob) in &map {
                let x = read_obs(&mut cx, oa, &st0, &[])?;
                let y = read_obs(&mut cx, ob, &st0, &[])?;
                if let (Some(x), Some(y)) = (x, y) {
                    pre_eqs.push(cx.eq_ext(x, y));
                }
            }
            let pre_t = cx.m.t.and(&pre_eqs);
            assume.push(F::T(pre_t));
            let t0 = Instant::now();
            let (oa, ta) = cx.run(&a, &side_a, &params, st0.clone())?;
            let traps_a: Vec<(Id, Id)> = std::mem::take(&mut cx.m.traps);
            let cut_a = std::mem::take(&mut cx.m.cutoffs);
            let (ob, tb) = cx.run(&b, &side_b, &params, st0.clone())?;
            let traps_b: Vec<(Id, Id)> = std::mem::take(&mut cx.m.traps);
            let cut_b = std::mem::take(&mut cx.m.cutoffs);
            let _ = t0;
            let mut binds = cx.binds(&a, &st0, Some(&oa));
            binds.extend(cx.binds(&b, &st0, Some(&ob)));
            binds.extend(param_binds(&params));
            for f in &p.pre {
                assume.push(F::Raw(f.clone(), binds.clone()));
            }
            let both_ok = cx.m.t.and2(oa.guard, ob.guard);
            let mut show: Vec<(String, Id)> = params.clone();
            for (n, ox, oy) in &map {
                if let (Some(x), Some(y)) = (
                    read_obs(&mut cx, ox, &st0, &[])?,
                    read_obs(&mut cx, oy, &st0, &[])?,
                ) {
                    show.push((format!("pre.a.{n}"), x));
                    if x != y {
                        show.push((format!("pre.b.{n}"), y));
                    }
                }
            }
            if observe.iter().any(|o| o == "trap") {
                let e = cx.m.t.eq(ta, tb);
                queries.push(Query {
                    name: "trap".into(),
                    assume: vec![],
                    goal: F::T(e),
                    show: show.clone(),
                    prelude: String::new(),
                });
            }
            if observe.iter().any(|o| o == "result") {
                let mut eqs = Vec::new();
                for (x, y) in oa.results.iter().zip(&ob.results) {
                    eqs.push(cx.eq_ext(*x, *y));
                }
                let e = cx.m.t.and(&eqs);
                let g = cx.m.t.implies(both_ok, e);
                let mut sh = show.clone();
                for (i, (x, y)) in oa.results.iter().zip(&ob.results).enumerate() {
                    sh.push((format!("a.result{i}"), *x));
                    sh.push((format!("b.result{i}"), *y));
                }
                queries.push(Query {
                    name: "result".into(),
                    assume: vec![],
                    goal: F::T(g),
                    show: sh,
                    prelude: String::new(),
                });
            }
            if observe
                .iter()
                .any(|o| o == "map" || o == "globals" || o == "memory")
            {
                for (n, ox, oy) in &map {
                    let x = read_obs(&mut cx, ox, &oa.st, &oa.results)?;
                    let y = read_obs(&mut cx, oy, &ob.st, &ob.results)?;
                    let (Some(x), Some(y)) = (x, y) else { continue };
                    let e = cx.eq_ext(x, y);
                    let g = cx.m.t.implies(both_ok, e);
                    if cx.m.t.as_bool(g) == Some(true) {
                        continue;
                    }
                    let mut sh = show.clone();
                    if !matches!(cx.m.t.sort(x), Sort::Mem(_)) {
                        sh.push((format!("post.a.{n}"), x));
                        sh.push((format!("post.b.{n}"), y));
                    }
                    queries.push(Query {
                        name: format!("map {n}"),
                        assume: vec![],
                        goal: F::T(g),
                        show: sh,
                        prelude: String::new(),
                    });
                }
            }
            for u in &p.unchanged_b {
                let o = cx.obs(&b, u)?;
                let (Some(x), Some(y)) = (
                    read_obs(&mut cx, &o, &st0, &[])?,
                    read_obs(&mut cx, &o, &ob.st, &ob.results)?,
                ) else {
                    continue;
                };
                let e = cx.m.t.eq(x, y);
                let g = cx.m.t.implies(ob.guard, e);
                queries.push(Query {
                    name: format!("frame {u}"),
                    assume: vec![],
                    goal: F::T(g),
                    show: show.clone(),
                    prelude: String::new(),
                });
            }
            if let Some(fr) = &p.frame_b {
                let k: usize = fr
                    .mem
                    .strip_prefix('m')
                    .context("frame mem")?
                    .parse()
                    .unwrap_or(0);
                let slot = cx.m.insts[b.main].mems[k];
                let mut ranges = Vec::new();
                for e in &fr.except {
                    let (o, n) = e.split_once(':').context("except OFF:N")?;
                    let o = parse_lit(o).context("offset")?.0;
                    let n: u64 = n.parse()?;
                    ranges.push(format!("(bvult (bvsub a!f #x{o:08x}) #x{n:08x})"));
                }
                let text = format!(
                    "(=> g (forall ((a!f (_ BitVec 32))) (=> (not (or false {})) (= (select post a!f) (select pre a!f)))))",
                    ranges.join(" ")
                );
                queries.push(Query {
                    name: format!("frame {}", fr.mem),
                    assume: vec![],
                    goal: F::Raw(
                        text,
                        vec![
                            ("g".into(), ob.guard),
                            ("pre".into(), st0.m[slot]),
                            ("post".into(), ob.st.m[slot]),
                        ],
                    ),
                    show: show.clone(),
                    prelude: String::new(),
                });
            }
            if observe.iter().any(|o| o == "hist") {
                let e = cx.m.t.eq(oa.st.h, ob.st.h);
                let g = cx.m.t.implies(both_ok, e);
                let ha = merge_hist(&mut cx, &traps_a);
                let hb = merge_hist(&mut cx, &traps_b);
                let both_trap = cx.m.t.and2(ta, tb);
                let e2 = cx.m.t.eq(ha, hb);
                let g2 = cx.m.t.implies(both_trap, e2);
                let gg = cx.m.t.and2(g, g2);
                if cx.m.t.as_bool(gg) != Some(true) {
                    queries.push(Query {
                        name: "calls".into(),
                        assume: vec![],
                        goal: F::T(gg),
                        show: show.clone(),
                        prelude: String::new(),
                    });
                }
            }
            complete_goal.extend(cut_a);
            complete_goal.extend(cut_b);
        }
        "post" | "bmc" => {
            let a = cx.side_c("", &side_a, &p.env, &p.contracts)?;
            add_loops(&mut cx, &a, &p.loops)?;
            let mut st0 = cx.m.initial(symbolic, "");
            env_data(&mut cx, &p.env, dir, &mut st0)?;
            if symbolic {
                keep(&mut cx, &a, &side_a, &mut st0)?;
            }
            let params = make_params(&mut cx, p, &a, &side_a, fixed)?;
            assume.extend(domain_assumptions(&mut cx, p, &params)?);
            let (o, trap) = cx.run(&a, &side_a, &params, st0.clone())?;
            if let Some(mo) = &p.mem_obs {
                let slot = if mo == "env" {
                    cx.m.env_mem
                        .context("mem_obs = env without environment memory")?
                } else {
                    *cx.m
                        .mem_imports
                        .get(mo)
                        .with_context(|| format!("no imported memory {mo}"))?
                };
                let so = cx.m.t.sort(st0.m[slot]);
                mem_prelude = format!(
                    "(declare-const |mem!old| {s})\n(declare-const |mem!post| {s})\n",
                    s = so.smt()
                );
                assume.push(F::Raw(
                    "(= |mem!old| m)".into(),
                    vec![("m".into(), st0.m[slot])],
                ));
                assume.push(F::Raw(
                    "(= |mem!post| m)".into(),
                    vec![("m".into(), o.st.m[slot])],
                ));
            }
            let mut binds = cx.binds(&a, &st0, Some(&o));
            binds.extend(param_binds(&params));
            let pre_binds = {
                let mut b = cx.binds(&a, &st0, None);
                b.extend(param_binds(&params));
                b
            };
            for f in &p.pre {
                assume.push(F::Raw(f.clone(), pre_binds.clone()));
            }
            let mut show: Vec<(String, Id)> = params.clone();
            show.extend(
                cx.binds(&a, &st0, None)
                    .into_iter()
                    .filter(|(_, t)| !matches!(cx.m.t.node(*t), super::term::N::Lit(..))),
            );
            base_show = show.clone();
            if !p.post.is_empty() {
                let posts: Vec<F> = p
                    .post
                    .iter()
                    .map(|f| F::Raw(f.clone(), binds.clone()))
                    .collect();
                let mut sh = show.clone();
                sh.extend(
                    o.results
                        .iter()
                        .enumerate()
                        .map(|(i, &r)| (format!("result{i}"), r)),
                );
                queries.push(Query {
                    name: "post".into(),
                    assume: vec![],
                    goal: F::implies(F::T(o.guard), F::And(posts)),
                    show: sh,
                    prelude: String::new(),
                });
            }
            if p.no_trap {
                let nt = cx.m.t.not(trap);
                queries.push(Query {
                    name: "no-trap".into(),
                    assume: vec![],
                    goal: F::T(nt),
                    show: show.clone(),
                    prelude: String::new(),
                });
            }
            for nc in &p.never_call {
                let events: Vec<Event> =
                    cx.m.events
                        .iter()
                        .filter(|e| {
                            let k = cx.m.hosts[e.host].key();
                            match nc.import.strip_suffix('*') {
                                Some(pfx) => k.starts_with(pfx),
                                None => k == nc.import,
                            }
                        })
                        .cloned()
                        .collect();
                let mut bad = Vec::new();
                for e in &events {
                    let mut eb: Vec<(String, Id)> = e
                        .args
                        .iter()
                        .enumerate()
                        .map(|(i, &x)| (format!("arg{i}"), x))
                        .collect();
                    // state at the call
                    for &k in &a.insts {
                        let inst = &cx.m.insts[k];
                        for (gi, &slot) in inst.globals.iter().enumerate() {
                            eb.push((
                                format!("g.{}", inst.m.global_name(gi as u32)),
                                e.state.g[slot],
                            ));
                        }
                    }
                    for (n, t) in &pre_binds {
                        eb.push((format!("old.{n}"), *t));
                    }
                    let allowed = match &nc.unless {
                        Some(u) => F::Raw(u.clone(), eb),
                        None => F::Raw("false".into(), vec![]),
                    };
                    bad.push(F::And(vec![F::T(e.guard), F::not(allowed)]));
                }
                let mut sh = show.clone();
                for (i, e) in events.iter().enumerate().take(8) {
                    for (j, &x) in e.args.iter().enumerate() {
                        sh.push((format!("call{i}.arg{j}"), x));
                    }
                }
                queries.push(Query {
                    name: format!("never-call {}", nc.import),
                    assume: vec![],
                    goal: F::not(F::Or(bad)),
                    show: sh,
                    prelude: String::new(),
                });
            }
            complete_goal.extend(std::mem::take(&mut cx.m.cutoffs));
        }
        k => bail!("unknown problem kind {k}"),
    }
    // loop obligations, one goal per kind
    let obl = std::mem::take(&mut cx.m.obligations);
    let mut kinds: Vec<String> = obl.iter().map(|o| o.0.clone()).collect();
    kinds.dedup();
    kinds.sort();
    kinds.dedup();
    for k in kinds {
        let fs: Vec<Id> = obl.iter().filter(|o| o.0 == k).map(|o| o.1).collect();
        let g = cx.m.t.and(&fs);
        queries.push(Query {
            name: k,
            assume: vec![],
            goal: F::T(g),
            show: base_show.clone(),
            prelude: String::new(),
        });
    }
    let symex_seconds = start.elapsed().as_secs_f64();
    if !complete_goal.is_empty() {
        let c = cx.m.t.or(&complete_goal);
        let nc = cx.m.t.not(c);
        queries.push(Query {
            name: "complete".into(),
            assume: vec![],
            goal: F::T(nc),
            show: vec![],
            prelude: String::new(),
        });
    }
    let mut answers = Vec::new();
    let work = if fixed.is_empty() {
        work
    } else {
        let tag: Vec<String> = fixed.iter().map(|(n, v)| format!("{n}{v}")).collect();
        work.join(tag.join("_"))
    };
    let prelude: String = mem_prelude.clone()
        + &p.defines
            .iter()
            .map(|d| format!("{d}\n"))
            .collect::<String>();
    for q in &mut queries {
        q.assume.extend(assume.iter().cloned());
        q.prelude = prelude.clone();
    }
    // all goals at once first; individually when that fails
    let (main_q, rest): (Vec<Query>, Vec<Query>) =
        queries.into_iter().partition(|q| q.name != "complete");
    let mut batched = false;
    if p.batch.unwrap_or(true) && main_q.len() > 1 {
        let all = Query {
            name: "all".into(),
            assume: assume.clone(),
            goal: F::And(main_q.iter().map(|q| q.goal.clone()).collect()),
            show: vec![],
            prelude: prelude.clone(),
        };
        let ans = solve::check(&cx.m.t, &all, &solver, (timeout / 10).max(3), &work)?;
        if ans.status == Status::Proved {
            answers.push(Answer {
                name: format!("all {} goals", main_q.len()),
                ..ans
            });
            batched = true;
        }
    }
    if !batched {
        for q in &main_q {
            answers.push(solve::check(&cx.m.t, q, &solver, timeout, &work)?);
        }
    }
    for q in &rest {
        answers.push(solve::check(&cx.m.t, q, &solver, timeout, &work)?);
    }
    let main: Vec<&Answer> = answers.iter().filter(|a| a.name != "complete").collect();
    let complete = answers
        .iter()
        .find(|a| a.name == "complete")
        .is_none_or(|a| a.status == Status::Proved);
    // A refutation is genuine when the refuted goal is a property of the
    // program (not a loop annotation) and no loop was over-approximated by
    // its invariant. Summarised checking loops keep refutations of the total-
    // correctness conjunction genuine (see `try_summarise`).
    let genuine =
        |a: &&Answer| a.status == Status::Refuted && !a.name.contains(" loop ") && !cx.m.cut;
    let verdict = if main.iter().any(genuine) {
        "refuted"
    } else if main.iter().any(|a| a.status == Status::Refuted) {
        "unknown"
    } else if main.iter().all(|a| a.status == Status::Proved) {
        if !complete {
            "bounded"
        } else if cx.m.partial {
            "partial"
        } else {
            "proved"
        }
    } else {
        "unknown"
    };
    let trust = match verdict {
        "proved" => {
            format!("SMT ({solver}): every goal unsat; symbolic executor and solver trusted")
        }
        "partial" => format!(
            "SMT ({solver}): every goal unsat, partial correctness only (a loop invariant without a measure)"
        ),
        "bounded" => format!(
            "SMT ({solver}): goals unsat for runs within unroll={} depth={}; longer runs not covered",
            cx.m.lim.unroll, cx.m.lim.depth
        ),
        "refuted" => format!("SMT ({solver}) model of a run violating the goal"),
        _ => String::new(),
    };
    Ok(Report {
        problem: pname,
        kind: p.kind.clone(),
        verdict: verdict.into(),
        trust,
        seconds: start.elapsed().as_secs_f64(),
        symex_seconds,
        symex_steps: cx.m.steps,
        terms: cx.m.t.len(),
        goals: answers,
        expect: p.expect.clone(),
        error: String::new(),
    })
}

fn merge_hist(cx: &mut Ctx, traps: &[(Id, Id)]) -> Id {
    let mut h = cx.m.t.hist_nil();
    for &(g, hh) in traps.iter().rev() {
        h = cx.m.t.ite(g, hh, h);
    }
    h
}

/// Read an observation; memory observations encoded as `Global(usize::MAX - slot)`
/// compare whole memories.
fn read_obs(cx: &mut Ctx, o: &Obs, st: &State, results: &[Id]) -> Result<Option<Id>> {
    if let Obs::Global(g) = o
        && *g > usize::MAX / 2
    {
        return Ok(Some(st.m[usize::MAX - g]));
    }
    let mut base = o;
    while let Obs::Slice(b, _, _) = base {
        base = b;
    }
    if matches!(base, Obs::Result(_)) && results.is_empty() {
        return Ok(None);
    }
    cx.read(o, st, results).map(Some)
}

fn make_params(
    cx: &mut Ctx,
    p: &Problem,
    a: &Inst,
    side: &Side,
    fixed: &[(String, u64)],
) -> Result<Vec<(String, Id)>> {
    if !p.params.is_empty() {
        return p
            .params
            .iter()
            .map(|q| {
                let w = param_sort(&q.ty)?;
                Ok(match fixed.iter().find(|f| f.0 == q.name) {
                    Some((_, v)) => (q.name.clone(), cx.m.t.lit(*v, w)),
                    None => (q.name.clone(), lift(cx, p, &q.name, w)?),
                })
            })
            .collect();
    }
    let entry = side.entry.clone().or_else(|| {
        (side.calls.len() == 1 && side.calls[0].args.is_empty()).then(|| side.calls[0].func.clone())
    });
    let Some(e) = entry else { return Ok(vec![]) };
    let (k, f) = cx.find_func(a, &e)?;
    let ty = cx.m.insts[k].m.func_ty(f).clone();
    ty.params
        .iter()
        .enumerate()
        .map(|(i, t)| {
            let n = cx.m.insts[k]
                .m
                .local_names
                .get(&f)
                .and_then(|ns| ns.get(&(i as u32)).cloned())
                .unwrap_or_else(|| format!("p{i}"));
            Ok(match fixed.iter().find(|f| f.0 == n) {
                Some((_, v)) => (n.clone(), cx.m.t.lit(*v, t.width())),
                None => (n.clone(), lift(cx, p, &n, t.width())?),
            })
        })
        .collect()
}

fn add_loops(cx: &mut Ctx, s: &Inst, loops: &[LoopAnn]) -> Result<()> {
    for l in loops {
        let (k, f) = cx.find_func(s, &l.func)?;
        cx.m.invariants.insert(
            (k, f, l.r#loop),
            super::exec::LoopSpec {
                inv: l.invariant.clone(),
                decreases: l.decreases.clone(),
                parts: l.parts.clone(),
                measures: l.measures.clone(),
            },
        );
    }
    Ok(())
}

/// A parameter: a variable, or for a parameter with a finite domain the `ite`
/// over its values (equal to the variable under the domain assumption,
/// `domain_assumptions`).
fn lift(cx: &mut Ctx, p: &Problem, name: &str, w: u32) -> Result<Id> {
    let v = cx.m.t.var(name, Sort::Bv(w));
    let Some(d) = p.domains.get(name) else {
        return Ok(v);
    };
    let vals = case_values(d)?;
    let mut acc = cx.m.t.lit(*vals.last().context("empty domain")?, w);
    for &k in vals.iter().rev().skip(1) {
        let kk = cx.m.t.lit(k, w);
        let c = cx.m.t.eq(v, kk);
        acc = cx.m.t.ite(c, kk, acc);
    }
    Ok(acc)
}

fn domain_assumptions(cx: &mut Ctx, p: &Problem, params: &[(String, Id)]) -> Result<Vec<F>> {
    let mut out = Vec::new();
    for (n, d) in &p.domains {
        let Some((_, t)) = params.iter().find(|x| &x.0 == n) else {
            continue;
        };
        if cx.m.t.as_lit(*t).is_some() {
            continue;
        }
        let w = cx.m.t.width(*t);
        let v = cx.m.t.var(n, Sort::Bv(w));
        let mut cs = Vec::new();
        for k in case_values(d)? {
            let kk = cx.m.t.lit(k, w);
            cs.push(cx.m.t.eq(v, kk));
        }
        out.push(F::T(cx.m.t.or(&cs)));
    }
    Ok(out)
}

/// Parameters by name and by position (`p0`, `p1`, …).
fn param_binds(params: &[(String, Id)]) -> Vec<(String, Id)> {
    let mut b = params.to_vec();
    for (i, (n, t)) in params.iter().enumerate() {
        let alias = format!("p{i}");
        if *n != alias && !params.iter().any(|x| x.0 == alias) {
            b.push((alias, *t));
        }
    }
    b
}

/// Restore the module-initialised bytes of the `keep` ranges of a side.
fn keep(cx: &mut Ctx, s: &Inst, side: &Side, st0: &mut State) -> Result<()> {
    for k in &side.keep {
        let parts: Vec<&str> = k.split(':').collect();
        let [m, off, n] = parts.as_slice() else {
            bail!("keep ranges are mK:OFF:N, not {k}")
        };
        let mi: usize = m.strip_prefix('m').context("keep")?.parse().unwrap_or(0);
        let off = parse_lit(off).context("offset")?.0;
        let n: u64 = n.parse()?;
        let module = cx.m.insts[s.main].m.clone();
        let slot = cx.m.insts[s.main].mems[mi];
        let mut mem = st0.m[slot];
        for a in off..off + n {
            let mut b = 0u8;
            for d in module.data.iter().filter(|d| d.mem as usize == mi) {
                if a >= d.offset && a < d.offset + d.bytes.len() as u64 {
                    b = d.bytes[(a - d.offset) as usize];
                }
            }
            let ai = cx.m.t.lit(a, 32);
            let v = cx.m.t.lit(b as u64, 8);
            mem = cx.m.t.store(mem, ai, v);
        }
        st0.m[slot] = mem;
    }
    Ok(())
}

/// Put the given bytes into the initial environment memory (as stores over
/// the arbitrary initial memory, so that fetches from them fold to literals).
fn env_data(cx: &mut Ctx, env: &EnvSpec, dir: &Path, st0: &mut State) -> Result<()> {
    if env.data.is_empty() {
        return Ok(());
    }
    let slot =
        cx.m.env_mem
            .context("env.data needs env.mem = \"array\" and mem.* imports")?;
    let mut mem = st0.m[slot];
    for d in &env.data {
        let addr = parse_lit(&d.addr).context("data address")?.0;
        let bytes = match (&d.file, &d.hex) {
            (Some(f), _) => std::fs::read(dir.join(f))?,
            (None, Some(h)) => {
                let h: String = h.chars().filter(|c| !c.is_whitespace()).collect();
                (0..h.len() / 2)
                    .map(|i| u8::from_str_radix(&h[2 * i..2 * i + 2], 16))
                    .collect::<Result<_, _>>()?
            }
            _ => bail!("data needs file or hex"),
        };
        for (i, b) in bytes.iter().enumerate() {
            let a = cx.m.t.lit(addr + i as u64, 64);
            let v = cx.m.t.lit(*b as u64, 8);
            mem = cx.m.t.store(mem, a, v);
        }
    }
    st0.m[slot] = mem;
    Ok(())
}

#[allow(dead_code)]
fn unused(_: Bv2, _: Rel) {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn schema_is_optional_and_parsed() {
        let p: Problem = toml::from_str("kind = \"post\"\n").unwrap();
        assert!(p.schema.is_none());
        let p: Problem =
            toml::from_str("schema = \"wasm-vc.problem.v1\"\nkind = \"equiv\"\n").unwrap();
        assert_eq!(p.schema.as_deref(), Some(SCHEMA));
        // unknown fields are still rejected
        assert!(toml::from_str::<Problem>("kind = \"post\"\nschem = \"x\"\n").is_err());
    }

    #[test]
    fn call_steps_default_repeat() {
        let p: Problem = toml::from_str(
            "kind = \"post\"\ncalls = [{ func = \"f\", args = [\"1\"] }, { func = \"g\", repeat = 3 }]\n",
        )
        .unwrap();
        assert_eq!(p.calls[0].repeat, 1);
        assert_eq!(p.calls[1].repeat, 3);
        assert!(p.calls[1].args.is_empty());
    }
}
