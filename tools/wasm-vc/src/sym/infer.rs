//! Loop invariant inference for P-locals problems (registers as i64 locals),
//! Houdini style: generate template candidates for every unannotated loop of
//! the entry function, check entry and preservation of each candidate under
//! the conjunction of all remaining ones, drop the failing ones, repeat to a
//! fixpoint. Templates (`v`, `w` written locals, `p`, `q` parameters, `F` a
//! specification function the postcondition mentions):
//!
//! * `v + F(w) = F(old p)` and `F(w) = F(old p)` (accumulator loops: sum, popcount);
//! * `F(v, w) = F(old p, old q)` (binary, e.g. gcd);
//! * `v ≠ 0`, `v ≤u old p`;
//! * measures: `v` for each written local (first that decreases on every back edge).
//!
//! The candidates are only hypotheses: the inferred invariant is then used as
//! an ordinary annotation, and every obligation is checked again.

use super::module::{Ins, Module, Ty};
use super::problem::{LoopAnn, Opts, Problem};
use super::solve::Status;
use anyhow::Result;
use std::collections::BTreeSet;
use std::path::Path;

fn loops(body: &[Ins], out: &mut Vec<(u32, BTreeSet<u32>)>) {
    for i in body {
        match i {
            Ins::Loop { id, body, .. } => {
                let mut w = BTreeSet::new();
                written(body, &mut w);
                out.push((*id, w));
                loops(body, out);
            }
            Ins::Block { body, .. } => loops(body, out),
            Ins::If { then, els, .. } => {
                loops(then, out);
                loops(els, out);
            }
            _ => {}
        }
    }
}

fn written(body: &[Ins], w: &mut BTreeSet<u32>) {
    for i in body {
        match i {
            Ins::LocalSet(l) | Ins::LocalTee(l) => {
                w.insert(*l);
            }
            Ins::Loop { body, .. } | Ins::Block { body, .. } => written(body, w),
            Ins::If { then, els, .. } => {
                written(then, w);
                written(els, w);
            }
            _ => {}
        }
    }
}

/// Specification functions (name, arity) defined in the problem and used in its postcondition.
fn spec_funs(p: &Problem) -> Vec<(String, usize)> {
    let post = p.post.join(" ");
    let mut out: Vec<(String, usize)> = Vec::new();
    for d in &p.defines {
        let rest = d
            .strip_prefix("(define-fun-rec ")
            .or_else(|| d.strip_prefix("(define-fun "))
            .or_else(|| d.strip_prefix("(declare-fun "));
        let Some(rest) = rest else { continue };
        let name = rest.split_whitespace().next().unwrap_or("").to_string();
        let arity = if d.starts_with("(declare-fun") {
            rest.matches("(_ BitVec").count().saturating_sub(1)
        } else {
            // ((a (_ BitVec 64)) (b …)) Sort …: the parameter list is the first group
            let params = rest[name.len()..].trim_start();
            let mut depth = 0;
            let mut n = 0;
            for c in params.chars() {
                match c {
                    '(' => {
                        depth += 1;
                        if depth == 2 {
                            n += 1;
                        }
                    }
                    ')' => {
                        depth -= 1;
                        if depth == 0 {
                            break;
                        }
                    }
                    _ => {}
                }
            }
            n
        };
        if post.contains(&format!("({name} ")) && (1..=2).contains(&arity) {
            out.push((name, arity));
        }
    }
    for (n, a) in [("gcd", 2), ("tri", 1), ("fact", 1), ("popcount", 1)] {
        if post.contains(&format!("({n} ")) && !out.iter().any(|x| x.0 == n) {
            out.push((n.into(), a));
        }
    }
    out
}

pub struct Inferred {
    pub loops: Vec<LoopAnn>,
    pub rounds: u32,
    pub note: String,
}

/// Infer invariants for the unannotated loops of the entry function.
pub fn infer(p: &Problem, dir: &Path, opts: &Opts) -> Result<Option<Inferred>> {
    if p.kind != "post" {
        return Ok(None);
    }
    let Some(entry) = &p.entry else {
        return Ok(None);
    };
    let Some(ms) = p.modules.last() else {
        return Ok(None);
    };
    let m = Module::load(&dir.join(&ms.wat))?;
    let f = m.find_func(entry)?;
    if f < m.n_imports() {
        return Ok(None);
    }
    let func = &m.funcs[(f - m.n_imports()) as usize];
    let ty = &m.types[func.ty as usize];
    let tys: Vec<Ty> = ty.params.iter().chain(&func.locals).copied().collect();
    let names = m.local_names.get(&f).cloned().unwrap_or_default();
    let name = |l: u32| names.get(&l).cloned().unwrap_or_else(|| format!("l{l}"));
    let fname = m.func_name(f);
    let mut ls = Vec::new();
    loops(&func.body, &mut ls);
    ls.retain(|(id, _)| {
        !p.loops
            .iter()
            .any(|l| l.r#loop == *id && (l.func == *entry || l.func == format!("${fname}")))
    });
    // P-locals loops only: every written local is an i64 register
    // (other loops, e.g. checking loops, are summarised or unrolled)
    ls.retain(|(_, w)| !w.is_empty() && w.iter().all(|&l| tys.get(l as usize) == Some(&Ty::I64)));
    if ls.is_empty() {
        return Ok(None);
    }
    let nparams = ty.params.len() as u32;
    let params: Vec<String> = (0..nparams)
        .filter(|&i| tys[i as usize] == Ty::I64)
        .map(name)
        .collect();
    let funs = spec_funs(p);
    let mut anns = Vec::new();
    for (id, w) in &ls {
        let wv: Vec<String> = w
            .iter()
            .filter(|&&l| tys.get(l as usize) == Some(&Ty::I64))
            .map(|&l| name(l))
            .collect();
        let mut vs = wv.clone();
        for q in &params {
            if !vs.contains(q) {
                vs.push(q.clone());
            }
        }
        let mut c = Vec::new();
        for (fun, ar) in &funs {
            if *ar == 1 {
                for p0 in &params {
                    for v2 in &wv {
                        c.push(format!("(= ({fun} {v2}) ({fun} old.{p0}))"));
                        for v1 in &wv {
                            if v1 != v2 {
                                c.push(format!("(= (bvadd {v1} ({fun} {v2})) ({fun} old.{p0}))"));
                            }
                        }
                    }
                }
            } else {
                for p0 in &params {
                    for p1 in &params {
                        if p0 == p1 {
                            continue;
                        }
                        for v1 in &vs {
                            for v2 in &vs {
                                if v1 != v2 {
                                    c.push(format!(
                                        "(= ({fun} {v1} {v2}) ({fun} old.{p0} old.{p1}))"
                                    ));
                                }
                            }
                        }
                    }
                }
            }
        }
        for v in &wv {
            c.push(format!("(distinct {v} #x0000000000000000)"));
            for p0 in &params {
                c.push(format!("(bvule {v} old.{p0})"));
            }
        }
        c.sort();
        c.dedup();
        anns.push(LoopAnn {
            func: format!("${fname}"),
            r#loop: *id,
            invariant: "true".into(),
            decreases: None,
            parts: c,
            measures: wv.clone(),
        });
    }
    // Houdini
    let mut q = p.clone();
    q.post = vec![];
    q.no_trap = false;
    q.never_call = vec![];
    q.batch = Some(false);
    q.infer = Some(false);
    let mut rounds = 0;
    let mut measures_ok: Vec<Option<String>> = vec![None; anns.len()];
    loop {
        rounds += 1;
        q.loops = p
            .loops
            .iter()
            .cloned()
            .chain(anns.iter().cloned())
            .collect();
        let r = super::problem::solve(&q, dir, opts)?;
        let mut dropped = false;
        for (k, a) in anns.iter_mut().enumerate() {
            let tag = format!("{fname} loop {}:", a.r#loop);
            let bad: BTreeSet<usize> = r
                .goals
                .iter()
                .filter(|g| {
                    g.name.starts_with(&tag)
                        && g.name.contains("invariant")
                        && g.status != Status::Proved
                })
                .filter_map(|g| g.name.rsplit_once('#').and_then(|x| x.1.parse().ok()))
                .collect();
            if !bad.is_empty() {
                dropped = true;
                a.parts = a
                    .parts
                    .iter()
                    .enumerate()
                    .filter(|(j, _)| !bad.contains(j))
                    .map(|x| x.1.clone())
                    .collect();
            }
            measures_ok[k] = r
                .goals
                .iter()
                .filter(|g| {
                    g.name.starts_with(&tag)
                        && g.name.contains("measure")
                        && g.status == Status::Proved
                })
                .filter_map(|g| {
                    g.name
                        .rsplit_once('#')
                        .and_then(|x| x.1.parse::<usize>().ok())
                })
                .min()
                .map(|j| a.measures[j].clone());
        }
        if !dropped || rounds >= 12 {
            break;
        }
    }
    let mut note = String::new();
    let out: Vec<LoopAnn> = anns
        .into_iter()
        .zip(measures_ok)
        .filter(|(a, _)| !a.parts.is_empty())
        .map(|(a, m)| {
            let inv = if a.parts.is_empty() {
                "true".to_string()
            } else {
                format!("(and true {})", a.parts.join(" "))
            };
            note.push_str(&format!(
                "loop {}: invariant {inv}; measure {}. ",
                a.r#loop,
                m.as_deref().unwrap_or("none")
            ));
            LoopAnn {
                func: a.func,
                r#loop: a.r#loop,
                invariant: inv,
                decreases: m,
                parts: vec![],
                measures: vec![],
            }
        })
        .collect();
    Ok(Some(Inferred {
        loops: out,
        rounds,
        note,
    }))
}
