//! The reduction plan, schema `silmaril.wasm-sim.reduce.v0` (`docs/projects/wasm-sim-reduction.md`): an
//! artifact (ELF), the functions with their System V contracts (SMT-LIB terms over `(reg r)` =
//! location after the call, `(old t)` = `t` at entry, `(mem8..64 a)`), loop cuts, Lean names,
//! and test vectors. The x86 reduction (`wasm-sim reduce`) reads these fields; the RV64
//! reduction reads the same file with its own extensions (`reads`, `writes`, `function.test`),
//! so unknown fields are accepted.

use anyhow::{Context, Result, bail};
use serde::Deserialize;
use std::collections::BTreeMap;
use std::path::Path;

pub const SCHEMA: &str = "silmaril.wasm-sim.reduce.v0";

#[derive(Deserialize, Clone, Debug)]
pub struct Plan {
    pub schema: String,
    pub id: String,
    #[serde(default)]
    pub title: String,
    pub root: String,
    /// SMT-LIB definitions used by the contracts.
    #[serde(default)]
    pub defs: BTreeMap<String, String>,
    pub artifact: Artifact,
    #[serde(default)]
    pub isa: Option<Isa>,
    #[serde(default)]
    pub sim: Option<SimDesc>,
    /// The argument registers of the root for test vectors (default `rdi rsi`).
    #[serde(default)]
    pub args: Vec<String>,
    #[serde(rename = "function")]
    pub functions: Vec<Function>,
    #[serde(default, rename = "test")]
    pub tests: Vec<Test>,
}

#[derive(Deserialize, Clone, Debug)]
pub struct Artifact {
    pub elf: String,
    #[serde(default)]
    pub source: Option<String>,
    #[serde(default)]
    pub build: Option<String>,
}

#[derive(Deserialize, Clone, Debug)]
pub struct Isa {
    #[serde(default)]
    pub model: String,
    #[serde(default)]
    pub machine: String,
    #[serde(default)]
    pub template: String,
}

#[derive(Deserialize, Clone, Debug)]
pub struct SimDesc {
    #[serde(default)]
    pub interface: String,
    #[serde(default)]
    pub representation: String,
    #[serde(default)]
    pub alternatives: Vec<AltSim>,
}

#[derive(Deserialize, Clone, Debug)]
pub struct AltSim {
    pub representation: String,
    #[serde(default)]
    pub wat: String,
}

#[derive(Deserialize, Clone, Debug)]
pub struct Function {
    pub name: String,
    #[serde(default = "tru")]
    pub requires: String,
    #[serde(default = "tru")]
    pub ensures: String,
    /// The Lean ISA statement (e.g. `Silmaril.Problems.WasmSim.isaF`).
    #[serde(default)]
    pub isa_lean: Option<String>,
    #[serde(default, rename = "cut")]
    pub cuts: Vec<Cut>,
    /// Lean names of the per-instruction route (`--granularity insn`), when stated/solved.
    #[serde(default)]
    pub insn: Option<InsnLean>,
    /// Lean names of the dispatcher route (the x86 P-inline with control flow), when solved.
    #[serde(default)]
    pub dispatch: Option<DispatchLean>,
    /// What is missing for this function (a `task` edge `isa/f ⇐ task/f`).
    #[serde(default)]
    pub task: Option<String>,
    /// Per-function decomposition (assume-guarantee): Wasm pieces for the segments between
    /// calls, composed with the callees' ISA goals.
    #[serde(default)]
    pub decomposed: Option<Decomposed>,
}

#[derive(Deserialize, Clone, Debug)]
pub struct Decomposed {
    #[serde(rename = "piece")]
    pub pieces: Vec<NamedPiece>,
    /// Callees whose `isa/<callee>` goals are assumed (their contracts).
    pub callees: Vec<String>,
    /// The composition theorem `pieces → callee goals → isa/f`.
    pub theorem: String,
}

#[derive(Deserialize, Clone, Debug)]
pub struct NamedPiece {
    pub id: String,
    pub statement: String,
    pub lean: String,
    #[serde(default)]
    pub solution: Option<String>,
}

/// The dispatcher route (loops): Wasm piece ⇒ x86 problem; with termination ⇒ ISA goal.
#[derive(Deserialize, Clone, Debug)]
pub struct DispatchLean {
    pub piece: String,
    #[serde(default)]
    pub piece_solution: Option<String>,
    pub x86: String,
    pub x86_of_piece: String,
    /// x86-side termination and frame (the piece is partial correctness).
    pub term: String,
    #[serde(default)]
    pub term_solution: Option<String>,
    /// The theorem `x86 → term → ISA goal`.
    pub isa_of: String,
    /// The Wasm termination piece (a ranking of the dispatcher) and the theorem `rank → term`.
    #[serde(default)]
    pub rank: Option<String>,
    #[serde(default)]
    pub rank_solution: Option<String>,
    #[serde(default)]
    pub term_of_rank: Option<String>,
}

/// The per-instruction route of one function: piece ⇒ x86 problem (P-calls soundness) ⇒ ISA goal.
#[derive(Deserialize, Clone, Debug)]
pub struct InsnLean {
    /// The Wasm piece (`Silmaril.Sim.Reduce.PCalls.Piece …`) and its solution.
    pub piece: String,
    #[serde(default)]
    pub piece_solution: Option<String>,
    #[serde(default)]
    pub piece_problem: Option<String>,
    /// Translation validity + method pieces of the instantiated module (`StepFns …`) and its proof.
    pub fns: String,
    #[serde(default)]
    pub fns_solution: Option<String>,
    /// The x86 problem (`XProblem …`) and the theorem `piece → x86`.
    pub x86: String,
    pub x86_of_piece: String,
    /// The theorem `x86 → ISA goal` (decoding, `ret`, System V contract).
    pub isa_of_x86: String,
}

fn tru() -> String {
    "true".into()
}

#[derive(Deserialize, Clone, Debug)]
pub struct Cut {
    /// Byte offset of the loop head from the function's entry.
    pub at: u64,
    pub invariant: String,
    #[serde(default)]
    pub decreases: Option<String>,
}

#[derive(Deserialize, Clone, Debug)]
pub struct Test {
    pub args: Vec<i64>,
}

pub fn read(p: &Path) -> Result<Plan> {
    let text = std::fs::read_to_string(p).with_context(|| format!("reading {}", p.display()))?;
    let plan: Plan = toml::from_str(&text).with_context(|| format!("parsing {}", p.display()))?;
    if plan.schema != SCHEMA {
        bail!(
            "{}: schema {:?}, expected {SCHEMA}",
            p.display(),
            plan.schema
        );
    }
    Ok(plan)
}
