//! SMT-LIB encodings of verification conditions and solver runs. Solvers are
//! oracles: their answers choose hints and report counterexamples, and Lean
//! checks every proof regardless.

use crate::term::B;
use crate::vc::{Config, Goal, Hyp, Vc};
use anyhow::{Context, Result};
use std::fmt::Write;
use std::process::Command;
use std::time::Instant;

pub fn script(vc: &Vc, cfg: &Config, with_hints: bool) -> String {
    let mut s = String::from(
        "(set-option :produce-unsat-cores true)\n(set-option :produce-models true)\n(set-logic ALL)\n",
    );
    for f in &cfg.fun {
        let args = vec!["(_ BitVec 32)"; f.arity].join(" ");
        writeln!(s, "(declare-fun {} ({args}) (_ BitVec 32))", f.name).unwrap();
    }
    if with_hints {
        for h in &cfg.hint {
            writeln!(s, "(assert (! {} :named ax_{}))", h.smt, h.name).unwrap();
        }
    }
    for v in &vc.vars {
        writeln!(
            s,
            "(declare-const {} (_ BitVec 32))",
            v.replace('\u{2080}', "_old")
        )
        .unwrap();
    }
    for (n, h) in &vc.hyps {
        let f = match h {
            Hyp::Cond(b, true) => b.smt(),
            Hyp::Cond(b, false) => B::Not(Box::new(b.clone())).smt(),
            Hyp::Inv(b) => b.smt(),
        };
        writeln!(s, "(assert (! {f} :named {n}))").unwrap();
    }
    let g = match &vc.goal {
        Goal::Prop(b) => b.smt(),
        Goal::Eq(l, r) => format!("(= {} {})", l.smt(), r.smt()),
        Goal::Lt(a, b) => format!("(bvult {} {})", a.smt(), b.smt()),
    };
    writeln!(s, "(assert (! (not {g}) :named goal))\n(check-sat)").unwrap();
    s
}

#[derive(Debug, Clone)]
pub struct Outcome {
    pub solver: String,
    /// `unsat` (the condition holds), `sat`, `unknown`, or an error.
    pub status: String,
    /// Named hints in the unsat core.
    pub core: Vec<String>,
    /// The model, for `sat`.
    pub model: String,
    pub seconds: f64,
}

fn command(solver: &str, file: &str) -> Command {
    let mut c = Command::new(solver);
    match solver {
        "z3" => {
            c.args(["-T:20", file]);
        }
        "cvc5" => {
            c.args(["--tlimit=20000", "--lang=smt2", file]);
        }
        _ => {
            c.args(["--time-limit=20000", file]);
        }
    }
    c
}

/// Run one solver on one condition: check satisfiability of its negation,
/// then ask for the core (if `unsat`) or the model (if `sat`).
pub fn run(solver: &str, vc: &Vc, cfg: &Config, dir: &std::path::Path) -> Result<Outcome> {
    let base = script(vc, cfg, true);
    let file = dir.join(format!("{}.{solver}.smt2", vc.name));
    std::fs::write(&file, format!("{base}(get-unsat-core)\n(get-model)\n"))?;
    let start = Instant::now();
    let out = command(solver, file.to_str().context("path")?)
        .output()
        .with_context(|| format!("could not run {solver}"))?;
    let seconds = start.elapsed().as_secs_f64();
    let text = String::from_utf8_lossy(&out.stdout).to_string();
    let mut lines = text.lines();
    let status = lines.next().unwrap_or("error").trim().to_string();
    let rest: String = lines.collect::<Vec<_>>().join("\n");
    let mut core = Vec::new();
    let mut model = String::new();
    if status == "unsat" {
        if let Some(open) = rest.find('(') {
            let close = rest[open..].find(')').map_or(rest.len(), |c| open + c);
            core = rest[open + 1..close]
                .split_whitespace()
                .filter_map(|n| n.strip_prefix("ax_").map(str::to_string))
                .collect();
        }
    } else if status == "sat" {
        model = rest
            .lines()
            .filter(|l| !l.contains("error"))
            .collect::<Vec<_>>()
            .join("\n");
    }
    Ok(Outcome {
        solver: solver.to_string(),
        status,
        core,
        model,
        seconds,
    })
}

pub fn available(solver: &str) -> bool {
    Command::new(solver).arg("--version").output().is_ok()
}
