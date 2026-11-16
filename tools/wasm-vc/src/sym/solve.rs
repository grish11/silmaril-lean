//! Queries to SMT solvers. A query is a list of assumptions and a goal; the
//! solver is asked for a model of the assumptions and the negated goal:
//! `unsat` means the goal holds (`proved`, as far as the solver is trusted),
//! `sat` gives a counterexample.
//!
//! Formulas mix terms of the DAG and user text in SMT-LIB syntax; user text
//! refers to named terms through `let` bindings.

use super::term::{Id, Terms};
use anyhow::{Context, Result};
use serde::Serialize;
use std::collections::HashMap;
use std::process::{Command, Stdio};
use std::time::Instant;

#[derive(Clone, Debug)]
pub enum F {
    T(Id),
    /// SMT-LIB text with names bound to terms.
    Raw(String, Vec<(String, Id)>),
    And(Vec<F>),
    Or(Vec<F>),
    Not(Box<F>),
    Implies(Box<F>, Box<F>),
}

impl F {
    pub fn implies(a: F, b: F) -> F {
        F::Implies(Box::new(a), Box::new(b))
    }
    pub fn not(a: F) -> F {
        F::Not(Box::new(a))
    }
    fn ids(&self, out: &mut Vec<Id>) {
        match self {
            F::T(t) => out.push(*t),
            F::Raw(_, b) => out.extend(b.iter().map(|x| x.1)),
            F::And(v) | F::Or(v) => v.iter().for_each(|f| f.ids(out)),
            F::Not(a) => a.ids(out),
            F::Implies(a, b) => {
                a.ids(out);
                b.ids(out)
            }
        }
    }
    fn render(&self, names: &HashMap<Id, String>) -> String {
        match self {
            F::T(t) => names[t].clone(),
            F::Raw(s, b) => {
                if b.is_empty() {
                    s.clone()
                } else {
                    let bs: Vec<String> = b
                        .iter()
                        .map(|(n, t)| format!("({} {})", super::term::quote(n), names[t]))
                        .collect();
                    format!("(let ({}) {s})", bs.join(" "))
                }
            }
            F::And(v) if v.is_empty() => "true".into(),
            F::Or(v) if v.is_empty() => "false".into(),
            F::And(v) => format!(
                "(and {})",
                v.iter()
                    .map(|f| f.render(names))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            F::Or(v) => format!(
                "(or {})",
                v.iter()
                    .map(|f| f.render(names))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            F::Not(a) => format!("(not {})", a.render(names)),
            F::Implies(a, b) => format!("(=> {} {})", a.render(names), b.render(names)),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Query {
    pub name: String,
    pub assume: Vec<F>,
    pub goal: F,
    /// Terms whose values a counterexample should show.
    pub show: Vec<(String, Id)>,
    /// SMT-LIB text placed after the declarations (user definitions).
    pub prelude: String,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum Status {
    Proved,
    Refuted,
    Unknown,
}

#[derive(Clone, Debug, Serialize)]
pub struct Answer {
    pub name: String,
    pub status: Status,
    pub solver: String,
    pub seconds: f64,
    /// Counterexample values (name, SMT-LIB value) for `refuted`.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub model: Vec<(String, String)>,
    #[serde(skip_serializing_if = "String::is_empty")]
    pub note: String,
    /// Size of the query (DAG nodes, bytes of SMT-LIB).
    pub nodes: usize,
    pub bytes: usize,
}

/// The SMT-LIB script of a query.
pub fn script(t: &Terms, q: &Query) -> (String, usize) {
    let mut ids = Vec::new();
    for f in &q.assume {
        f.ids(&mut ids);
    }
    q.goal.ids(&mut ids);
    let shown: Vec<Id> = q.show.iter().map(|x| x.1).collect();
    ids.extend(&shown);
    ids.sort_unstable();
    ids.dedup();
    let (decls, defs, rn) = t.emit(&ids);
    let nodes = t.dag_size(&ids);
    let names: HashMap<Id, String> = ids.iter().copied().zip(rn).collect();
    let mut s = String::from("(set-option :produce-models true)\n(set-logic ALL)\n");
    s.push_str(&decls);
    s.push_str(&q.prelude);
    s.push_str(&defs);
    for f in &q.assume {
        s.push_str(&format!("(assert {})\n", f.render(&names)));
    }
    s.push_str(&format!(
        "(assert (not {}))\n(check-sat)\n",
        q.goal.render(&names)
    ));
    let mut s = with_prelude(s);
    if !q.show.is_empty() {
        let vs: Vec<String> = q.show.iter().map(|(_, i)| names[i].clone()).collect();
        s.push_str(&format!("(get-value ({}))\n", vs.join(" ")));
    }
    (s, nodes)
}

/// Specification functions of the reduced problems (64-bit): defined here
/// when a query mentions them. `gcd` is Euclid's algorithm on unsigned values
/// (`gcd a 0 = a`), `tri n` = 0 + 1 + … + n (mod 2^64), `fact` the factorial
/// (mod 2^64), `popcount` the number of one bits.
const PRELUDE: &[(&str, &str)] = &[
    (
        "gcd",
        "(define-fun-rec gcd ((a (_ BitVec 64)) (b (_ BitVec 64))) (_ BitVec 64) (ite (= b #x0000000000000000) a (gcd b (bvurem a b))))",
    ),
    (
        "tri",
        "(define-fun-rec tri ((n (_ BitVec 64))) (_ BitVec 64) (ite (= n #x0000000000000000) #x0000000000000000 (bvadd n (tri (bvsub n #x0000000000000001)))))",
    ),
    (
        "fact",
        "(define-fun-rec fact ((n (_ BitVec 64))) (_ BitVec 64) (ite (= n #x0000000000000000) #x0000000000000001 (bvmul n (fact (bvsub n #x0000000000000001)))))",
    ),
];

fn popcount_def() -> String {
    let bits: Vec<String> = (0..64)
        .map(|i| format!("((_ zero_extend 63) ((_ extract {i} {i}) x))"))
        .collect();
    format!(
        "(define-fun popcount ((x (_ BitVec 64))) (_ BitVec 64) (bvadd {}))",
        bits.join(" ")
    )
}

fn with_prelude(s: String) -> String {
    let mut defs = String::new();
    for (n, d) in PRELUDE {
        let user = s.contains(&format!("(define-fun-rec {n} "))
            || s.contains(&format!("(define-fun {n} "))
            || s.contains(&format!("(declare-fun {n} "));
        if !user && s.contains(&format!("({n} ")) {
            defs.push_str(d);
            defs.push('\n');
        }
    }
    if s.contains("(popcount ")
        && !s.contains("(define-fun-rec popcount ")
        && !s.contains("(define-fun popcount ")
        && !s.contains("(declare-fun popcount ")
    {
        defs.push_str(&popcount_def());
        defs.push('\n');
    }
    if defs.is_empty() {
        return s;
    }
    let at = s.find("(set-logic ALL)\n").map_or(0, |p| p + 16);
    let mut out = s;
    out.insert_str(at, &defs);
    out
}

fn solver_cmd(solver: &str, file: &str, timeout: u64) -> Command {
    let mut c = Command::new("nice");
    c.arg("-n").arg("10");
    match solver {
        "z3" => {
            c.args(["z3", &format!("-T:{timeout}"), file]);
        }
        "cvc5" => {
            c.args([
                "cvc5",
                &format!("--tlimit={}", timeout * 1000),
                "--lang=smt2",
                "--produce-models",
                file,
            ]);
        }
        "bitwuzla" => {
            c.args([
                "bitwuzla",
                &format!("--time-limit={}", timeout * 1000),
                "--produce-models",
                file,
            ]);
        }
        other => {
            c.args([other, file]);
        }
    }
    c
}

/// Split a `(get-value ((a v) (b w)))` answer into its pairs.
fn parse_values(text: &str) -> Vec<String> {
    // top-level pairs inside the outer parentheses
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut start = None;
    for (i, ch) in text.char_indices() {
        match ch {
            '(' => {
                depth += 1;
                if depth == 2 {
                    start = Some(i);
                }
            }
            ')' => {
                if depth == 2
                    && let Some(s) = start.take()
                {
                    out.push(text[s..=i].to_string());
                }
                depth -= 1;
            }
            _ => {}
        }
    }
    out
}

pub fn check(
    t: &Terms,
    q: &Query,
    solver: &str,
    timeout: u64,
    dir: &std::path::Path,
) -> Result<Answer> {
    let (text, nodes) = script(t, q);
    std::fs::create_dir_all(dir)?;
    let safe: String = q
        .name
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '-' || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect();
    let file = dir.join(format!("{safe}.smt2"));
    std::fs::write(&file, &text)?;
    let start = Instant::now();
    let out = solver_cmd(solver, file.to_str().context("path")?, timeout)
        .stdin(Stdio::null())
        .output()
        .with_context(|| format!("could not run {solver}"))?;
    let seconds = start.elapsed().as_secs_f64();
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    let first = stdout.lines().next().unwrap_or("").trim().to_string();
    let rest: String = stdout.lines().skip(1).collect::<Vec<_>>().join("\n");
    let (status, note) = match first.as_str() {
        "unsat" => (Status::Proved, String::new()),
        "sat" => (Status::Refuted, String::new()),
        "unknown" | "timeout" => (Status::Unknown, first.clone()),
        _ => (
            Status::Unknown,
            format!(
                "solver output: {} {}",
                stdout.chars().take(300).collect::<String>(),
                String::from_utf8_lossy(&out.stderr)
                    .chars()
                    .take(300)
                    .collect::<String>()
            ),
        ),
    };
    let (status, note) = if status == Status::Refuted && q.prelude.contains("(declare-fun ") {
        (
            Status::Unknown,
            "countermodel interprets uninterpreted spec functions; not a refutation".to_string(),
        )
    } else {
        (status, note)
    };
    let mut model = Vec::new();
    if status == Status::Refuted {
        let vals = parse_values(&rest);
        for ((n, _), v) in q.show.iter().zip(vals) {
            // `(name value)`: drop the name part
            let inner = v.trim_start_matches('(').trim_end_matches(')');
            let val = match inner.find(|c: char| c.is_whitespace()) {
                Some(_) => {
                    // value is the last token or parenthesised group
                    let s = v[1..v.len() - 1].trim();
                    if let Some(p) = s.rfind(" #") {
                        s[p + 1..].to_string()
                    } else {
                        s.rsplit(' ').next().unwrap_or(s).to_string()
                    }
                }
                None => inner.to_string(),
            };
            model.push((n.clone(), val));
        }
    }
    Ok(Answer {
        name: q.name.clone(),
        status,
        solver: solver.to_string(),
        seconds,
        model,
        note,
        nodes,
        bytes: text.len(),
    })
}
