//! Terms over `i32` values (`T`) and formulas (`B`), read from SMT-LIB-style
//! annotations or produced by symbolic execution, printed as SMT-LIB and as
//! Lean (`BitVec 32` and `Bool`/`Prop`).

use crate::sexp::Sexp;
use anyhow::{Context, Result, bail};
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum T {
    Var(String),
    Lit(u32),
    /// SMT-LIB bit-vector operator (`bvadd`, `bvsub`, …) on arguments.
    Op(String, Vec<T>),
    /// An uninterpreted (spec-level) function, e.g. `tri`.
    Fun(String, Vec<T>),
    Ite(Box<B>, Box<T>, Box<T>),
    /// The `i32` encoding of a Boolean (`bool32`).
    Bool32(Box<B>),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum B {
    True,
    False,
    /// Comparison (`=`, `distinct`, `bvslt`, `bvsle`, `bvult`, `bvule`).
    Cmp(String, Box<T>, Box<T>),
    Not(Box<B>),
    And(Vec<B>),
    Or(Vec<B>),
    Implies(Box<B>, Box<B>),
}

pub const BV_OPS: [&str; 10] = [
    "bvadd", "bvsub", "bvmul", "bvand", "bvor", "bvxor", "bvshl", "bvashr", "bvlshr", "bvneg",
];

/// How annotation identifiers resolve.
pub struct Env<'a> {
    /// Function symbols of the specification (name to arity).
    pub funs: &'a BTreeMap<String, usize>,
    /// `result` is allowed.
    pub result: bool,
}

pub fn lit_of(atom: &str) -> Option<u32> {
    if let Some(h) = atom.strip_prefix("#x") {
        return u32::from_str_radix(h, 16).ok().filter(|_| h.len() == 8);
    }
    if let Some(b) = atom.strip_prefix("#b") {
        return u32::from_str_radix(b, 2).ok().filter(|_| b.len() == 32);
    }
    None
}

impl T {
    pub fn var(name: &str) -> T {
        T::Var(name.to_string())
    }

    pub fn op(name: &str, args: Vec<T>) -> T {
        T::Op(name.to_string(), args)
    }

    pub fn from_sexp(s: &Sexp, env: &Env) -> Result<T> {
        match s {
            Sexp::Atom(a) => {
                if let Some(v) = lit_of(a) {
                    Ok(T::Lit(v))
                } else if a == "result" && !env.result {
                    bail!("`result` is only allowed in @ensures")
                } else if a
                    .chars()
                    .next()
                    .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
                {
                    Ok(T::Var(a.clone()))
                } else {
                    bail!("unsupported term atom {a}")
                }
            }
            Sexp::List(l) => {
                let head = l.first().and_then(Sexp::atom).context("term head")?;
                let args = &l[1..];
                if head == "_" {
                    // (_ bvN 32)
                    let v = args
                        .first()
                        .and_then(Sexp::atom)
                        .and_then(|a| a.strip_prefix("bv"));
                    let w = args.get(1).and_then(Sexp::atom);
                    if let (Some(v), Some("32")) = (v, w) {
                        return Ok(T::Lit(v.parse::<u64>()? as u32));
                    }
                    bail!("only (_ bvN 32) literals are supported");
                }
                if head == "old" {
                    let [Sexp::Atom(x)] = args else {
                        bail!("(old x) takes a variable")
                    };
                    return Ok(T::Var(format!("{x}\u{2080}")));
                }
                if head == "ite" {
                    let [c, a, b] = args else {
                        bail!("ite takes three arguments")
                    };
                    return Ok(T::Ite(
                        Box::new(B::from_sexp(c, env)?),
                        Box::new(T::from_sexp(a, env)?),
                        Box::new(T::from_sexp(b, env)?),
                    ));
                }
                let targs = args
                    .iter()
                    .map(|a| T::from_sexp(a, env))
                    .collect::<Result<Vec<_>>>()?;
                if BV_OPS.contains(&head) {
                    let arity = if head == "bvneg" { 1 } else { 2 };
                    if targs.len() != arity {
                        bail!("{head} takes {arity} arguments");
                    }
                    return Ok(T::Op(head.to_string(), targs));
                }
                if head == "bvnot" && targs.len() == 1 {
                    return Ok(T::Op(head.to_string(), targs));
                }
                if let Some(&n) = env.funs.get(head) {
                    if n != targs.len() {
                        bail!("{head} takes {n} arguments");
                    }
                    return Ok(T::Fun(head.to_string(), targs));
                }
                bail!("unknown function {head}")
            }
            Sexp::Str(_) => bail!("strings are not terms"),
        }
    }

    pub fn subst(&self, m: &BTreeMap<String, T>) -> T {
        match self {
            T::Var(v) => m.get(v).cloned().unwrap_or_else(|| self.clone()),
            T::Lit(_) => self.clone(),
            T::Op(o, a) => T::Op(o.clone(), a.iter().map(|x| x.subst(m)).collect()),
            T::Fun(f, a) => T::Fun(f.clone(), a.iter().map(|x| x.subst(m)).collect()),
            T::Ite(c, a, b) => T::Ite(
                Box::new(c.subst(m)),
                Box::new(a.subst(m)),
                Box::new(b.subst(m)),
            ),
            T::Bool32(b) => T::Bool32(Box::new(b.subst(m))),
        }
    }

    pub fn vars(&self, out: &mut Vec<String>) {
        match self {
            T::Var(v) => {
                if !out.contains(v) {
                    out.push(v.clone());
                }
            }
            T::Lit(_) => {}
            T::Op(_, a) | T::Fun(_, a) => a.iter().for_each(|x| x.vars(out)),
            T::Ite(c, a, b) => {
                c.vars(out);
                a.vars(out);
                b.vars(out);
            }
            T::Bool32(b) => b.vars(out),
        }
    }

    pub fn smt(&self) -> String {
        match self {
            T::Var(v) => smt_name(v),
            T::Lit(v) => format!("#x{v:08x}"),
            T::Op(o, a) | T::Fun(o, a) => {
                let args: Vec<String> = a.iter().map(T::smt).collect();
                format!("({o} {})", args.join(" "))
            }
            T::Ite(c, a, b) => format!("(ite {} {} {})", c.smt(), a.smt(), b.smt()),
            T::Bool32(b) => format!("(ite {} #x00000001 #x00000000)", b.smt()),
        }
    }

    /// Lean `BitVec 32` syntax. `funs` maps spec functions to Lean names.
    pub fn lean(&self, funs: &BTreeMap<String, String>) -> String {
        let bin = |sym: &str, a: &[T]| format!("({} {sym} {})", a[0].lean(funs), a[1].lean(funs));
        let shift = |method: &str, a: &[T]| match &a[1] {
            T::Lit(k) => format!("({}{method}{})", a[0].lean(funs), k % 32),
            b => format!("({}{method}({}.toNat % 32))", a[0].lean(funs), b.lean(funs)),
        };
        match self {
            T::Var(v) => v.clone(),
            T::Lit(v) => format!("({v} : BitVec 32)"),
            T::Op(o, a) => match o.as_str() {
                "bvadd" => bin("+", a),
                "bvsub" => bin("-", a),
                "bvmul" => bin("*", a),
                "bvand" => bin("&&&", a),
                "bvor" => bin("|||", a),
                "bvxor" => bin("^^^", a),
                "bvshl" => shift(" <<< ", a),
                "bvlshr" => shift(" >>> ", a),
                "bvashr" => match &a[1] {
                    T::Lit(k) => format!("({}.sshiftRight {})", a[0].lean(funs), k % 32),
                    b => format!(
                        "({}.sshiftRight ({}.toNat % 32))",
                        a[0].lean(funs),
                        b.lean(funs)
                    ),
                },
                "bvneg" => format!("(-{})", a[0].lean(funs)),
                "bvnot" => format!("(~~~{})", a[0].lean(funs)),
                other => format!(
                    "({other} {})",
                    a.iter().map(|x| x.lean(funs)).collect::<Vec<_>>().join(" ")
                ),
            },
            T::Fun(f, a) => {
                let name = funs.get(f).cloned().unwrap_or_else(|| f.clone());
                format!(
                    "({name} {})",
                    a.iter().map(|x| x.lean(funs)).collect::<Vec<_>>().join(" ")
                )
            }
            T::Ite(c, a, b) => format!(
                "(if {} then {} else {})",
                c.lean_bool(funs),
                a.lean(funs),
                b.lean(funs)
            ),
            T::Bool32(b) => format!("(bool32 {})", b.lean_bool(funs)),
        }
    }
}

fn smt_name(v: &str) -> String {
    v.replace('\u{2080}', "_old")
}

impl B {
    pub fn from_sexp(s: &Sexp, env: &Env) -> Result<B> {
        match s {
            Sexp::Atom(a) if a == "true" => Ok(B::True),
            Sexp::Atom(a) if a == "false" => Ok(B::False),
            Sexp::List(l) => {
                let head = l.first().and_then(Sexp::atom).context("formula head")?;
                let args = &l[1..];
                let two = |f: &dyn Fn(T, T) -> B| -> Result<B> {
                    let [a, b] = args else {
                        bail!("{head} takes two arguments")
                    };
                    Ok(f(T::from_sexp(a, env)?, T::from_sexp(b, env)?))
                };
                let cmp = |op: &str, a: T, b: T| B::Cmp(op.to_string(), Box::new(a), Box::new(b));
                match head {
                    "=" | "distinct" | "bvslt" | "bvsle" | "bvult" | "bvule" => {
                        two(&|a, b| cmp(head, a, b))
                    }
                    "bvsgt" => two(&|a, b| cmp("bvslt", b, a)),
                    "bvsge" => two(&|a, b| cmp("bvsle", b, a)),
                    "bvugt" => two(&|a, b| cmp("bvult", b, a)),
                    "bvuge" => two(&|a, b| cmp("bvule", b, a)),
                    "not" => {
                        let [a] = args else {
                            bail!("not takes one argument")
                        };
                        Ok(B::Not(Box::new(B::from_sexp(a, env)?)))
                    }
                    "and" | "or" => {
                        let xs = args
                            .iter()
                            .map(|a| B::from_sexp(a, env))
                            .collect::<Result<Vec<_>>>()?;
                        Ok(if head == "and" { B::And(xs) } else { B::Or(xs) })
                    }
                    "=>" => {
                        let [a, b] = args else {
                            bail!("=> takes two arguments")
                        };
                        Ok(B::Implies(
                            Box::new(B::from_sexp(a, env)?),
                            Box::new(B::from_sexp(b, env)?),
                        ))
                    }
                    _ => bail!("unknown formula head {head}"),
                }
            }
            _ => bail!("unsupported formula {s}"),
        }
    }

    pub fn subst(&self, m: &BTreeMap<String, T>) -> B {
        match self {
            B::True | B::False => self.clone(),
            B::Cmp(o, a, b) => B::Cmp(o.clone(), Box::new(a.subst(m)), Box::new(b.subst(m))),
            B::Not(a) => B::Not(Box::new(a.subst(m))),
            B::And(xs) => B::And(xs.iter().map(|x| x.subst(m)).collect()),
            B::Or(xs) => B::Or(xs.iter().map(|x| x.subst(m)).collect()),
            B::Implies(a, b) => B::Implies(Box::new(a.subst(m)), Box::new(b.subst(m))),
        }
    }

    pub fn vars(&self, out: &mut Vec<String>) {
        match self {
            B::True | B::False => {}
            B::Cmp(_, a, b) => {
                a.vars(out);
                b.vars(out);
            }
            B::Not(a) => a.vars(out),
            B::And(xs) | B::Or(xs) => xs.iter().for_each(|x| x.vars(out)),
            B::Implies(a, b) => {
                a.vars(out);
                b.vars(out);
            }
        }
    }

    pub fn smt(&self) -> String {
        match self {
            B::True => "true".into(),
            B::False => "false".into(),
            B::Cmp(o, a, b) => format!("({o} {} {})", a.smt(), b.smt()),
            B::Not(a) => format!("(not {})", a.smt()),
            B::And(xs) if xs.is_empty() => "true".into(),
            B::Or(xs) if xs.is_empty() => "false".into(),
            B::And(xs) => format!(
                "(and {})",
                xs.iter().map(B::smt).collect::<Vec<_>>().join(" ")
            ),
            B::Or(xs) => format!(
                "(or {})",
                xs.iter().map(B::smt).collect::<Vec<_>>().join(" ")
            ),
            B::Implies(a, b) => format!("(=> {} {})", a.smt(), b.smt()),
        }
    }

    /// Lean `Bool` syntax, in the form the `Silmaril.WasmSpec.Ops` equations produce.
    pub fn lean_bool(&self, funs: &BTreeMap<String, String>) -> String {
        match self {
            B::True => "true".into(),
            B::False => "false".into(),
            B::Cmp(o, a, b) => {
                let (a, b) = (a.lean(funs), b.lean(funs));
                match o.as_str() {
                    "=" => format!("({a} == {b})"),
                    "distinct" => format!("({a} != {b})"),
                    "bvslt" => format!("({a}.slt {b})"),
                    "bvsle" => format!("({a}.sle {b})"),
                    "bvult" => format!("({a}.ult {b})"),
                    _ => format!("({a}.ule {b})"),
                }
            }
            B::Not(a) => format!("(!{})", a.lean_bool(funs)),
            B::And(xs) if xs.is_empty() => "true".into(),
            B::Or(xs) if xs.is_empty() => "false".into(),
            B::And(xs) => format!(
                "({})",
                xs.iter()
                    .map(|x| x.lean_bool(funs))
                    .collect::<Vec<_>>()
                    .join(" && ")
            ),
            B::Or(xs) => format!(
                "({})",
                xs.iter()
                    .map(|x| x.lean_bool(funs))
                    .collect::<Vec<_>>()
                    .join(" || ")
            ),
            B::Implies(a, b) => format!("(!{} || {})", a.lean_bool(funs), b.lean_bool(funs)),
        }
    }

    /// Lean `Prop` syntax.
    pub fn lean(&self, funs: &BTreeMap<String, String>) -> String {
        match self {
            B::True => "True".into(),
            B::False => "False".into(),
            B::Cmp(o, a, b) if o == "=" => format!("{} = {}", a.lean(funs), b.lean(funs)),
            B::Cmp(o, a, b) if o == "distinct" => format!("{} ≠ {}", a.lean(funs), b.lean(funs)),
            B::Cmp(..) => format!("{} = true", self.lean_bool(funs)),
            B::Not(a) => format!("¬({})", a.lean(funs)),
            B::And(xs) if xs.is_empty() => "True".into(),
            B::Or(xs) if xs.is_empty() => "False".into(),
            B::And(xs) => xs
                .iter()
                .map(|x| format!("({})", x.lean(funs)))
                .collect::<Vec<_>>()
                .join(" ∧ "),
            B::Or(xs) => xs
                .iter()
                .map(|x| format!("({})", x.lean(funs)))
                .collect::<Vec<_>>()
                .join(" ∨ "),
            B::Implies(a, b) => format!("({}) → ({})", a.lean(funs), b.lean(funs)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sexp;

    #[test]
    fn reads_and_prints_annotation_terms() {
        let funs = BTreeMap::from([("tri".to_string(), 1)]);
        let env = Env {
            funs: &funs,
            result: false,
        };
        let b = B::from_sexp(
            &sexp::parse("(= (bvadd acc (tri n)) (tri (old n)))").unwrap(),
            &env,
        )
        .unwrap();
        assert_eq!(b.smt(), "(= (bvadd acc (tri n)) (tri n_old))");
        let names = BTreeMap::from([("tri".to_string(), "triBV".to_string())]);
        assert_eq!(b.lean(&names), "(acc + (triBV n)) = (triBV n₀)");
        let g = B::from_sexp(&sexp::parse("(bvsgt x #x00000000)").unwrap(), &env).unwrap();
        assert_eq!(g.lean_bool(&names), "((0 : BitVec 32).slt x)");
        assert!(T::from_sexp(&sexp::parse("result").unwrap(), &env).is_err());
    }
}
