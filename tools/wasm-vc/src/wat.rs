//! A WAT subset: one module of `i32` functions with locals, integer
//! arithmetic, comparisons, `if`, `block`, `loop`, `br`, `br_if` and calls of
//! imported functions. Folded and flat instruction forms are both accepted and
//! flattened as the WAT text format specifies.

use crate::sexp::{self, Annotation, Sexp};
use anyhow::{Context, Result, bail};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Bin {
    Add,
    Sub,
    Mul,
    And,
    Or,
    Xor,
    Shl,
    ShrS,
    ShrU,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Rel {
    Eq,
    Ne,
    LtS,
    LtU,
    GtS,
    GtU,
    LeS,
    LeU,
    GeS,
    GeU,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Instr {
    LocalGet(usize),
    LocalSet(usize),
    LocalTee(usize),
    Const(u32),
    Bin(Bin),
    Eqz,
    Rel(Rel),
    /// `if (result i32)` (`result = true`) or without a result.
    If {
        result: bool,
        then: Vec<Instr>,
        els: Vec<Instr>,
    },
    Block {
        result: bool,
        body: Vec<Instr>,
    },
    Loop {
        result: bool,
        body: Vec<Instr>,
    },
    Br(u32),
    BrIf(u32),
    Call(usize),
    Drop,
}

impl Instr {
    pub fn is_straight(&self) -> bool {
        !matches!(
            self,
            Instr::If { .. }
                | Instr::Block { .. }
                | Instr::Loop { .. }
                | Instr::Br(_)
                | Instr::BrIf(_)
                | Instr::Call(_)
        )
    }
}

#[derive(Clone, Debug, Default)]
pub struct Annotations {
    pub requires: Vec<Sexp>,
    pub ensures: Vec<Sexp>,
    pub invariant: Vec<Sexp>,
    pub decreases: Option<Sexp>,
}

#[derive(Clone, Debug)]
pub struct Func {
    pub name: String,
    pub params: Vec<String>,
    /// Declared locals (after the parameters).
    pub locals: Vec<String>,
    pub result: bool,
    pub body: Vec<Instr>,
    pub ann: Annotations,
}

impl Func {
    /// Parameters, then declared locals.
    pub fn all_locals(&self) -> Vec<String> {
        self.params.iter().chain(&self.locals).cloned().collect()
    }
}

#[derive(Clone, Debug)]
pub struct Import {
    pub name: String,
    pub params: usize,
    pub assume: Option<Sexp>,
}

#[derive(Clone, Debug)]
pub struct Module {
    pub imports: Vec<Import>,
    pub funcs: Vec<Func>,
}

fn atom(s: &Sexp) -> Option<&str> {
    s.atom()
}

fn parse_u32(text: &str) -> Result<u32> {
    let t = text.replace('_', "");
    let (neg, t) = match t.strip_prefix('-') {
        Some(r) => (true, r.to_string()),
        None => (false, t.trim_start_matches('+').to_string()),
    };
    let v: u64 = if let Some(h) = t.strip_prefix("0x") {
        u64::from_str_radix(h, 16)?
    } else {
        t.parse()?
    };
    if v > u64::from(u32::MAX) {
        bail!("i32 constant {text} out of range");
    }
    let v = v as u32;
    Ok(if neg { v.wrapping_neg() } else { v })
}

struct Scope<'a> {
    locals: &'a [String],
    funcs: &'a [String],
    labels: Vec<Option<String>>,
}

impl Scope<'_> {
    fn local(&self, s: &Sexp) -> Result<usize> {
        let a = atom(s).context("expected a local index")?;
        if let Some(name) = a.strip_prefix('$') {
            self.locals
                .iter()
                .position(|l| l == name)
                .with_context(|| format!("unknown local ${name}"))
        } else {
            Ok(a.parse()?)
        }
    }

    fn label(&self, s: &Sexp) -> Result<u32> {
        let a = atom(s).context("expected a label")?;
        if let Some(name) = a.strip_prefix('$') {
            let pos = self
                .labels
                .iter()
                .rev()
                .position(|l| l.as_deref() == Some(name))
                .with_context(|| format!("unknown label ${name}"))?;
            Ok(pos as u32)
        } else {
            Ok(a.parse()?)
        }
    }

    fn func(&self, s: &Sexp) -> Result<usize> {
        let a = atom(s).context("expected a function index")?;
        if let Some(name) = a.strip_prefix('$') {
            self.funcs
                .iter()
                .position(|l| l == name)
                .with_context(|| format!("unknown function ${name}"))
        } else {
            Ok(a.parse()?)
        }
    }
}

fn plain(op: &str) -> Option<Instr> {
    Some(match op {
        "i32.add" => Instr::Bin(Bin::Add),
        "i32.sub" => Instr::Bin(Bin::Sub),
        "i32.mul" => Instr::Bin(Bin::Mul),
        "i32.and" => Instr::Bin(Bin::And),
        "i32.or" => Instr::Bin(Bin::Or),
        "i32.xor" => Instr::Bin(Bin::Xor),
        "i32.shl" => Instr::Bin(Bin::Shl),
        "i32.shr_s" => Instr::Bin(Bin::ShrS),
        "i32.shr_u" => Instr::Bin(Bin::ShrU),
        "i32.eqz" => Instr::Eqz,
        "i32.eq" => Instr::Rel(Rel::Eq),
        "i32.ne" => Instr::Rel(Rel::Ne),
        "i32.lt_s" => Instr::Rel(Rel::LtS),
        "i32.lt_u" => Instr::Rel(Rel::LtU),
        "i32.gt_s" => Instr::Rel(Rel::GtS),
        "i32.gt_u" => Instr::Rel(Rel::GtU),
        "i32.le_s" => Instr::Rel(Rel::LeS),
        "i32.le_u" => Instr::Rel(Rel::LeU),
        "i32.ge_s" => Instr::Rel(Rel::GeS),
        "i32.ge_u" => Instr::Rel(Rel::GeU),
        "drop" => Instr::Drop,
        _ => return None,
    })
}

/// `(result i32)` at the start of a block's items; returns whether present and
/// how many items it used. A label name may come first.
fn block_header(items: &[Sexp]) -> Result<(Option<String>, bool, usize)> {
    let mut i = 0;
    let mut label = None;
    if let Some(a) = items.first().and_then(atom)
        && let Some(n) = a.strip_prefix('$')
    {
        label = Some(n.to_string());
        i = 1;
    }
    let mut result = false;
    if let Some(r) = items.get(i)
        && r.head() == Some("result")
    {
        let l = r.list().unwrap_or_default();
        if l.len() != 2 || atom(&l[1]) != Some("i32") {
            bail!("only (result i32) block types are supported");
        }
        result = true;
        i += 1;
    }
    Ok((label, result, i))
}

/// Flatten a sequence of instructions (folded or flat) into `out`.
fn instrs(items: &[Sexp], scope: &mut Scope, out: &mut Vec<Instr>) -> Result<()> {
    let mut i = 0;
    while i < items.len() {
        let item = &items[i];
        i += 1;
        match item {
            Sexp::List(l) => folded(l, scope, out)?,
            Sexp::Atom(op) => {
                let op = op.as_str();
                let imm = items.get(i);
                match op {
                    "local.get" | "local.set" | "local.tee" => {
                        let x = scope.local(imm.context("missing local")?)?;
                        i += 1;
                        out.push(match op {
                            "local.get" => Instr::LocalGet(x),
                            "local.set" => Instr::LocalSet(x),
                            _ => Instr::LocalTee(x),
                        });
                    }
                    "i32.const" => {
                        out.push(Instr::Const(parse_u32(
                            imm.and_then(atom).context("missing constant")?,
                        )?));
                        i += 1;
                    }
                    "br" | "br_if" => {
                        let l = scope.label(imm.context("missing label")?)?;
                        i += 1;
                        out.push(if op == "br" {
                            Instr::Br(l)
                        } else {
                            Instr::BrIf(l)
                        });
                    }
                    "call" => {
                        out.push(Instr::Call(scope.func(imm.context("missing function")?)?));
                        i += 1;
                    }
                    "block" | "loop" | "if" => {
                        bail!("flat `{op}` … `end` is not supported; use the folded form")
                    }
                    _ => out
                        .push(plain(op).with_context(|| format!("unsupported instruction {op}"))?),
                }
            }
            Sexp::Str(_) => bail!("unexpected string in instructions"),
        }
    }
    Ok(())
}

fn folded(l: &[Sexp], scope: &mut Scope, out: &mut Vec<Instr>) -> Result<()> {
    let op = l
        .first()
        .and_then(atom)
        .context("expected an instruction")?;
    match op {
        "block" | "loop" => {
            let (label, result, used) = block_header(&l[1..])?;
            scope.labels.push(label);
            let mut body = Vec::new();
            instrs(&l[1 + used..], scope, &mut body)?;
            scope.labels.pop();
            out.push(if op == "block" {
                Instr::Block { result, body }
            } else {
                Instr::Loop { result, body }
            });
        }
        "if" => {
            let (label, result, used) = block_header(&l[1..])?;
            let rest = &l[1 + used..];
            let mut cond = Vec::new();
            let mut then = Vec::new();
            let mut els = Vec::new();
            for part in rest {
                match part.head() {
                    Some("then") => {
                        scope.labels.push(label.clone());
                        instrs(&part.list().unwrap_or_default()[1..], scope, &mut then)?;
                        scope.labels.pop();
                    }
                    Some("else") => {
                        scope.labels.push(label.clone());
                        instrs(&part.list().unwrap_or_default()[1..], scope, &mut els)?;
                        scope.labels.pop();
                    }
                    _ => instrs(std::slice::from_ref(part), scope, &mut cond)?,
                }
            }
            out.extend(cond);
            out.push(Instr::If { result, then, els });
        }
        _ => {
            // `(op imm? args…)`: arguments first, then the operator.
            let takes_imm = matches!(
                op,
                "local.get" | "local.set" | "local.tee" | "i32.const" | "br" | "br_if" | "call"
            );
            let args = if takes_imm { &l[2..] } else { &l[1..] };
            for a in args {
                instrs(std::slice::from_ref(a), scope, out)?;
            }
            let head = if takes_imm { &l[..2] } else { &l[..1] };
            instrs(head, scope, out)?;
        }
    }
    Ok(())
}

/// Parse a module and attach its annotations: `@requires`/`@ensures` to the
/// function that follows them, `@invariant`/`@decreases` to the function that
/// contains them, `@assume <import> <term>` to the named import.
pub fn parse_module(src: &str) -> Result<Module> {
    let (top, anns) = sexp::parse_with_annotations(src)?;
    let fields = match top.list() {
        Some([Sexp::Atom(m), rest @ ..]) if m == "module" => rest,
        _ => bail!("expected (module …)"),
    };
    let offsets = sexp::func_offsets(src);
    let mut func_names = Vec::new();
    let mut imports = Vec::new();
    for f in fields {
        if f.head() == Some("import") {
            let l = f.list().unwrap_or_default();
            let func = l
                .iter()
                .find(|x| x.head() == Some("func"))
                .context("only function imports are supported")?;
            let fl = func.list().unwrap_or_default();
            let name = fl
                .get(1)
                .and_then(atom)
                .and_then(|a| a.strip_prefix('$'))
                .context("imports need a $name")?;
            let params = fl
                .iter()
                .filter(|x| x.head() == Some("param"))
                .map(|x| x.list().map_or(0, |p| p.len() - 1))
                .sum();
            func_names.push(name.to_string());
            imports.push(Import {
                name: name.to_string(),
                params,
                assume: None,
            });
        }
    }
    let mut funcs = Vec::new();
    for f in fields {
        if f.head() != Some("func") {
            continue;
        }
        let l = f.list().unwrap_or_default();
        let name = l
            .get(1)
            .and_then(atom)
            .and_then(|a| a.strip_prefix('$'))
            .context("functions need a $name")?;
        func_names.push(name.to_string());
        let mut params = Vec::new();
        let mut locals = Vec::new();
        let mut result = false;
        let mut body_start = 2;
        for (k, x) in l.iter().enumerate().skip(2) {
            match x.head() {
                Some("export") => {}
                Some("param") | Some("local") => {
                    let p = x.list().unwrap_or_default();
                    let n = p
                        .get(1)
                        .and_then(atom)
                        .and_then(|a| a.strip_prefix('$'))
                        .context("params and locals need $names")?;
                    if p.get(2).and_then(atom) != Some("i32") || p.len() != 3 {
                        bail!("only named i32 params and locals are supported");
                    }
                    if x.head() == Some("param") {
                        params.push(n.to_string());
                    } else {
                        locals.push(n.to_string());
                    }
                }
                Some("result") => result = true,
                _ => {
                    body_start = k;
                    break;
                }
            }
            body_start = k + 1;
        }
        funcs.push((
            name.to_string(),
            params,
            locals,
            result,
            l[body_start..].to_vec(),
        ));
    }
    let mut out = Vec::new();
    for (idx, (name, params, locals, result, body_sexps)) in funcs.into_iter().enumerate() {
        let all: Vec<String> = params.iter().chain(&locals).cloned().collect();
        let mut scope = Scope {
            locals: &all,
            funcs: &func_names,
            labels: vec![None],
        };
        let mut body = Vec::new();
        instrs(&body_sexps, &mut scope, &mut body).with_context(|| format!("in ${name}"))?;
        out.push(Func {
            name,
            params,
            locals,
            result,
            body,
            ann: Annotations::default(),
        });
        let _ = idx;
    }
    attach(&mut out, &mut imports, &anns, &offsets)?;
    Ok(Module {
        imports,
        funcs: out,
    })
}

fn attach(
    funcs: &mut [Func],
    imports: &mut [Import],
    anns: &[Annotation],
    offsets: &[usize],
) -> Result<()> {
    if offsets.len() != funcs.len() {
        bail!("could not locate every (func …) in the source");
    }
    for a in anns {
        match a.key.as_str() {
            "requires" | "ensures" => {
                let k = offsets
                    .iter()
                    .position(|&o| o > a.offset)
                    .context("@requires/@ensures must precede a function")?;
                let t = sexp::parse(&a.text)?;
                if a.key == "requires" {
                    funcs[k].ann.requires.push(t);
                } else {
                    funcs[k].ann.ensures.push(t);
                }
            }
            "invariant" | "decreases" => {
                let k = offsets
                    .iter()
                    .rposition(|&o| o < a.offset)
                    .context("@invariant must be inside a function")?;
                let t = sexp::parse(&a.text)?;
                if a.key == "invariant" {
                    funcs[k].ann.invariant.push(t);
                } else {
                    funcs[k].ann.decreases = Some(t);
                }
            }
            "assume" => {
                let (name, term) = a
                    .text
                    .split_once(char::is_whitespace)
                    .context("@assume <import> <term>")?;
                let imp = imports
                    .iter_mut()
                    .find(|i| i.name == name)
                    .with_context(|| format!("@assume names unknown import {name}"))?;
                imp.assume = Some(sexp::parse(term)?);
            }
            other => bail!("unknown annotation @{other}"),
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn flattens_folded_loops_and_resolves_names() {
        let m = parse_module(
            "(module ;; @ensures (= result n)\n (func $s (param $n i32) (result i32) (local $a i32)
               (block $done (loop $again
                 ;; @invariant true
                 (br_if $done (i32.eqz (local.get $n)))
                 (local.set $a (i32.add (local.get $a) (local.get $n)))
                 (br $again)))
               (local.get $a)))",
        )
        .unwrap();
        let f = &m.funcs[0];
        assert_eq!(f.params, vec!["n"]);
        assert_eq!(f.locals, vec!["a"]);
        assert_eq!(f.ann.ensures.len(), 1);
        assert_eq!(f.ann.invariant.len(), 1);
        let Instr::Block { body, .. } = &f.body[0] else {
            panic!()
        };
        let Instr::Loop { body, .. } = &body[0] else {
            panic!()
        };
        assert_eq!(body[..3], [Instr::LocalGet(0), Instr::Eqz, Instr::BrIf(1)]);
        assert_eq!(body.last(), Some(&Instr::Br(0)));
        assert_eq!(f.body[1], Instr::LocalGet(1));
    }

    #[test]
    fn constants_wrap() {
        assert_eq!(parse_u32("-1").unwrap(), u32::MAX);
        assert_eq!(parse_u32("0x8000_0000").unwrap(), 0x8000_0000);
        assert!(parse_u32("0x1_0000_0000").is_err());
    }
}
