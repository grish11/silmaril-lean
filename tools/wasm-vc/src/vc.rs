//! Symbolic execution of the supported program shapes into verification
//! conditions, and the per-entry configuration (`vc.toml`).

use crate::term::{B, Env, T};
use crate::wat::{Bin, Func, Instr, Module, Rel};
use anyhow::{Context, Result, bail};
use serde::Deserialize;
use std::collections::BTreeMap;

#[derive(Debug, Deserialize, Clone)]
#[serde(deny_unknown_fields)]
pub struct Config {
    /// The library entry (`Silmaril/WasmSpec/<entry>`).
    pub entry: String,
    /// The annotated WAT file, relative to the entry directory.
    pub source: String,
    /// The WAT function to verify.
    pub func: String,
    /// Its Lean `Func` declaration in the entry namespace.
    pub lean_func: String,
    /// The specification to prove (default `Spec`).
    #[serde(default = "default_spec")]
    pub spec: String,
    /// Extra Lean modules to import (lemmas named by hints).
    #[serde(default)]
    pub imports: Vec<String>,
    #[serde(default)]
    pub fun: Vec<FunDecl>,
    #[serde(default)]
    pub hint: Vec<Hint>,
}

fn default_spec() -> String {
    "Spec".into()
}

/// A specification function: SMT name, arity, Lean name.
#[derive(Debug, Deserialize, Clone)]
#[serde(deny_unknown_fields)]
pub struct FunDecl {
    pub name: String,
    pub arity: usize,
    pub lean: String,
}

/// A fact about specification functions: an SMT axiom (named in unsat cores)
/// and the Lean tactic that brings the corresponding lemma into context;
/// `{v}` stands for a variable of the condition.
#[derive(Debug, Deserialize, Clone)]
#[serde(deny_unknown_fields)]
pub struct Hint {
    pub name: String,
    pub smt: String,
    pub lean: String,
}

impl Config {
    pub fn funs(&self) -> BTreeMap<String, usize> {
        self.fun.iter().map(|f| (f.name.clone(), f.arity)).collect()
    }

    pub fn lean_names(&self) -> BTreeMap<String, String> {
        self.fun
            .iter()
            .map(|f| (f.name.clone(), f.lean.clone()))
            .collect()
    }
}

/// A hypothesis of a verification condition.
#[derive(Clone, Debug)]
pub enum Hyp {
    /// A branch condition, true or false (`hc`).
    Cond(B, bool),
    /// The loop invariant (`hi`).
    Inv(B),
}

#[derive(Clone, Debug)]
pub enum Goal {
    Prop(B),
    /// `lhs = rhs` on `i32` values.
    Eq(T, T),
    /// The measure decreases: `new.toNat < old.toNat`.
    Lt(T, T),
}

#[derive(Clone, Debug)]
pub struct Vc {
    pub name: String,
    pub vars: Vec<String>,
    pub hyps: Vec<(String, Hyp)>,
    pub goal: Goal,
}

/// The program shapes the Lean templates support.
#[derive(Clone, Debug)]
pub enum Shape {
    /// Straight-line code returning one `i32`.
    Straight { body: Vec<Instr> },
    /// Straight-line code, then `if (result i32)` with straight-line branches.
    Branch {
        pre: Vec<Instr>,
        cond: B,
        then: Vec<Instr>,
        els: Vec<Instr>,
    },
    /// `block (loop P1 (br_if 1) P2 (br 0)) POST`.
    Loop {
        p1: Vec<Instr>,
        cond: B,
        p2: Vec<Instr>,
        post: Vec<Instr>,
        inv: B,
        measure: T,
        /// Locals after `P2` (the next iteration's state).
        next: Vec<T>,
    },
}

#[derive(Clone, Debug)]
pub struct Analysis {
    pub func: Func,
    /// Parameter names as initial values (`x₀`).
    pub params0: Vec<String>,
    pub locals: Vec<String>,
    pub ensures: T,
    pub shape: Shape,
    pub vcs: Vec<Vc>,
}

/// Run straight-line code on a symbolic stack and locals.
pub fn exec(code: &[Instr], stack: &mut Vec<T>, locals: &mut [T]) -> Result<()> {
    let pop = |s: &mut Vec<T>| s.pop().context("stack underflow");
    for i in code {
        match i {
            Instr::LocalGet(x) => stack.push(locals.get(*x).context("local index")?.clone()),
            Instr::LocalSet(x) => *locals.get_mut(*x).context("local index")? = pop(stack)?,
            Instr::LocalTee(x) => {
                let v = stack.last().context("stack underflow")?.clone();
                *locals.get_mut(*x).context("local index")? = v;
            }
            Instr::Const(c) => stack.push(T::Lit(*c)),
            Instr::Drop => {
                pop(stack)?;
            }
            Instr::Eqz => {
                let a = pop(stack)?;
                stack.push(T::Bool32(Box::new(B::Cmp(
                    "=".into(),
                    Box::new(a),
                    Box::new(T::Lit(0)),
                ))));
            }
            Instr::Bin(op) => {
                let b = pop(stack)?;
                let a = pop(stack)?;
                let name = match op {
                    Bin::Add => "bvadd",
                    Bin::Sub => "bvsub",
                    Bin::Mul => "bvmul",
                    Bin::And => "bvand",
                    Bin::Or => "bvor",
                    Bin::Xor => "bvxor",
                    Bin::Shl => "bvshl",
                    Bin::ShrS => "bvashr",
                    Bin::ShrU => "bvlshr",
                };
                stack.push(T::op(name, vec![a, b]));
            }
            Instr::Rel(r) => {
                let b = pop(stack)?;
                let a = pop(stack)?;
                let (op, x, y) = match r {
                    Rel::Eq => ("=", a, b),
                    Rel::Ne => ("distinct", a, b),
                    Rel::LtS => ("bvslt", a, b),
                    Rel::GtS => ("bvslt", b, a),
                    Rel::LeS => ("bvsle", a, b),
                    Rel::GeS => ("bvsle", b, a),
                    Rel::LtU => ("bvult", a, b),
                    Rel::GtU => ("bvult", b, a),
                    Rel::LeU => ("bvule", a, b),
                    Rel::GeU => ("bvule", b, a),
                };
                stack.push(T::Bool32(Box::new(B::Cmp(
                    op.into(),
                    Box::new(x),
                    Box::new(y),
                ))));
            }
            other => bail!("not straight-line code: {other:?}"),
        }
    }
    Ok(())
}

fn straight(code: &[Instr]) -> bool {
    code.iter().all(Instr::is_straight)
}

/// The condition left alone on the stack by `code`.
fn condition(code: &[Instr], locals: &mut [T]) -> Result<B> {
    let mut stack = Vec::new();
    exec(code, &mut stack, locals)?;
    match stack.as_slice() {
        [T::Bool32(b)] => Ok((**b).clone()),
        _ => bail!("a branch condition must be one comparison or eqz result, alone on the stack"),
    }
}

fn result_of(code: &[Instr], locals: &mut [T]) -> Result<T> {
    let mut stack = Vec::new();
    exec(code, &mut stack, locals)?;
    match stack.as_slice() {
        [r] => Ok(r.clone()),
        _ => bail!("straight-line code must leave exactly one i32 result"),
    }
}

pub fn subst_locals(names: &[String], values: &[T]) -> BTreeMap<String, T> {
    names.iter().cloned().zip(values.iter().cloned()).collect()
}

/// Analyse the configured function: shape, ensures and verification conditions.
/// `invariant` overrides the `@invariant`/`@decreases` annotations (used by the
/// agentic loop when it proposes one).
pub fn analyse(module: &Module, cfg: &Config, invariant: Option<(B, T)>) -> Result<Analysis> {
    let func = module
        .funcs
        .iter()
        .find(|f| f.name == cfg.func)
        .with_context(|| format!("no function ${}", cfg.func))?
        .clone();
    if !func.result {
        bail!("${} must return one i32", func.name);
    }
    let funs = cfg.funs();
    let env = Env {
        funs: &funs,
        result: true,
    };
    for r in &func.ann.requires {
        if B::from_sexp(r, &env)? != B::True {
            bail!(
                "only `@requires true` is supported (the specification form Computes is unconditional)"
            );
        }
    }
    let ens = match func.ann.ensures.as_slice() {
        [e] => B::from_sexp(e, &env)?,
        _ => bail!("exactly one @ensures (= result <term>) is required"),
    };
    let B::Cmp(op, lhs, rhs) = ens else {
        bail!("@ensures must be (= result <term>)")
    };
    if op != "=" || *lhs != T::var("result") {
        bail!("@ensures must be (= result <term>)");
    }
    let params0: Vec<String> = func.params.iter().map(|p| format!("{p}\u{2080}")).collect();
    let to_old: BTreeMap<String, T> = func
        .params
        .iter()
        .zip(&params0)
        .map(|(p, p0)| (p.clone(), T::var(p0)))
        .collect();
    let ensures = rhs.subst(&to_old);
    let locals = func.all_locals();
    let mut init: Vec<T> = params0.iter().map(|p| T::var(p)).collect();
    init.extend(func.locals.iter().map(|_| T::Lit(0)));
    let eq = |name: &str, vars: Vec<String>, hyps: Vec<(String, Hyp)>, l: T| Vc {
        name: name.into(),
        vars,
        hyps,
        goal: Goal::Eq(l, ensures.clone()),
    };

    let body = func.body.clone();
    let (shape, vcs) = if straight(&body) {
        let r = result_of(&body, &mut init.clone())?;
        (
            Shape::Straight { body },
            vec![eq("vc_post", params0.clone(), vec![], r)],
        )
    } else if let Some((
        Instr::If {
            result: true,
            then,
            els,
        },
        pre,
    )) = body.split_last()
        && straight(pre)
        && straight(then)
        && straight(els)
    {
        let mut l = init.clone();
        let cond = condition(pre, &mut l)?;
        let rt = result_of(then, &mut l.clone())?;
        let re = result_of(els, &mut l.clone())?;
        let vcs = vec![
            eq(
                "vc_then",
                params0.clone(),
                vec![("hc".into(), Hyp::Cond(cond.clone(), true))],
                rt,
            ),
            eq(
                "vc_else",
                params0.clone(),
                vec![("hc".into(), Hyp::Cond(cond.clone(), false))],
                re,
            ),
        ];
        (
            Shape::Branch {
                pre: pre.to_vec(),
                cond,
                then: then.clone(),
                els: els.clone(),
            },
            vcs,
        )
    } else if let [
        Instr::Block {
            result: false,
            body: inner,
        },
        post @ ..,
    ] = body.as_slice()
        && let [
            Instr::Loop {
                result: false,
                body: lb,
            },
        ] = inner.as_slice()
        && straight(post)
        && let Some(k) = lb.iter().position(|i| *i == Instr::BrIf(1))
        && lb.last() == Some(&Instr::Br(0))
        && straight(&lb[..k])
        && straight(&lb[k + 1..lb.len() - 1])
    {
        let (p1, p2) = (&lb[..k], &lb[k + 1..lb.len() - 1]);
        let lenv = Env {
            funs: &funs,
            result: false,
        };
        let (inv, measure) = match invariant {
            Some(x) => x,
            None => {
                let inv = match func.ann.invariant.as_slice() {
                    [] => bail!("the loop needs an @invariant (or an agent proposal)"),
                    xs => B::And(
                        xs.iter()
                            .map(|x| B::from_sexp(x, &lenv))
                            .collect::<Result<_>>()?,
                    ),
                };
                let inv = match inv {
                    B::And(mut xs) if xs.len() == 1 => xs.remove(0),
                    b => b,
                };
                let m = func
                    .ann
                    .decreases
                    .as_ref()
                    .context("the loop needs @decreases <term>")?;
                (inv, T::from_sexp(m, &lenv)?)
            }
        };
        let vars0 = || params0.iter().chain(&locals).cloned().collect::<Vec<_>>();
        let state: Vec<T> = locals.iter().map(|l| T::var(l)).collect();
        let mut after1 = state.clone();
        let cond = condition(p1, &mut after1)?;
        let mut next = after1.clone();
        let mut leftover = Vec::new();
        exec(p2, &mut leftover, &mut next)?;
        if !leftover.is_empty() {
            bail!("the loop body must leave the stack empty before `br 0`");
        }
        let r = result_of(post, &mut after1.clone())?;
        let at = |vals: &[T]| subst_locals(&locals, vals);
        let hi = ("hi".to_string(), Hyp::Inv(inv.clone()));
        let vcs = vec![
            Vc {
                name: "vc_init".into(),
                vars: params0.clone(),
                hyps: vec![],
                goal: Goal::Prop(inv.subst(&at(&init))),
            },
            eq(
                "vc_exit",
                vars0(),
                vec![("hc".into(), Hyp::Cond(cond.clone(), true)), hi.clone()],
                r,
            ),
            Vc {
                name: "vc_step".into(),
                vars: vars0(),
                hyps: vec![("hc".into(), Hyp::Cond(cond.clone(), false)), hi.clone()],
                goal: Goal::Prop(inv.subst(&at(&next))),
            },
            Vc {
                name: "vc_dec".into(),
                vars: vars0(),
                hyps: vec![("hc".into(), Hyp::Cond(cond.clone(), false)), hi],
                goal: Goal::Lt(measure.subst(&at(&next)), measure.clone()),
            },
        ];
        (
            Shape::Loop {
                p1: p1.to_vec(),
                cond,
                p2: p2.to_vec(),
                post: post.to_vec(),
                inv,
                measure,
                next,
            },
            vcs,
        )
    } else {
        bail!(
            "unsupported program shape: use straight-line code, a final `if (result i32)`, \
             or `block (loop … br_if 1 … br 0) …`"
        );
    };
    Ok(Analysis {
        func,
        params0,
        locals,
        ensures,
        shape,
        vcs,
    })
}
