//! Lean statements and proofs for annotated-WAT problems (the reductions'
//! format), through Silmaril's `wat_spec!` macro and the verified VC generator
//! `wpc` (`Silmaril/Wasm/WatSpec`, `Silmaril/Wasm/Logic/VC`): the problem's function
//! is quoted with its `@requires`/`@ensures`/`@invariant` annotations
//! translated from SMT-LIB into Lean `BitVec` terms, and `A.vc` is attempted
//! with `wat_vc`. The Lean kernel checks the result; nothing here is trusted.
//!
//! Fragment (that of `wat_spec!`/`wpc`): one function, `i32`/`i64`
//! parameters and locals, at most one result, integer straight-line code,
//! `block`/`loop`/`if`/`br`/`br_if`/`return`/`select`; no calls, no
//! `br_table`, no conversions (`wrap`/`extend`). Other problems are reported
//! as outside the fragment.

use crate::sexp::{self, Sexp};
use anyhow::{Context, Result, bail};
use std::path::Path;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Ty {
    Bool,
    Bv(u32),
}

struct Tr<'a> {
    /// Names and their widths (parameters, locals, `result`).
    vars: &'a [(String, u32)],
    funs_used: Vec<String>,
}

fn lit_lean(digits: &str, radix: u32, w: u32) -> Result<String> {
    let v = u128::from_str_radix(digits, radix)?;
    Ok(format!("(0x{v:x}#{w})"))
}

impl Tr<'_> {
    fn bv(&mut self, s: &Sexp) -> Result<(String, u32)> {
        match self.term(s)? {
            (t, Ty::Bv(w)) => Ok((t, w)),
            (t, Ty::Bool) => bail!("expected a bit-vector, got the formula {t}"),
        }
    }

    fn prop(&mut self, s: &Sexp) -> Result<String> {
        match self.term(s)? {
            (t, Ty::Bool) => Ok(t),
            (t, _) => bail!("expected a formula, got the term {t}"),
        }
    }

    fn term(&mut self, s: &Sexp) -> Result<(String, Ty)> {
        match s {
            Sexp::Atom(a) => {
                if let Some(h) = a.strip_prefix("#x") {
                    return Ok((
                        lit_lean(h, 16, 4 * h.len() as u32)?,
                        Ty::Bv(4 * h.len() as u32),
                    ));
                }
                if let Some(b) = a.strip_prefix("#b") {
                    return Ok((lit_lean(b, 2, b.len() as u32)?, Ty::Bv(b.len() as u32)));
                }
                match a.as_str() {
                    "true" => return Ok(("True".into(), Ty::Bool)),
                    "false" => return Ok(("False".into(), Ty::Bool)),
                    _ => {}
                }
                let name = a.replace("old.", "old_");
                let (_, w) = self
                    .vars
                    .iter()
                    .find(|(n, _)| *n == name || *n == a.as_str())
                    .with_context(|| format!("unknown name {a}"))?;
                Ok((name, Ty::Bv(*w)))
            }
            Sexp::Str(_) => bail!("string in a formula"),
            Sexp::List(l) => {
                // ((_ extract i j) x), ((_ zero_extend n) x), ((_ sign_extend n) x)
                if let Some(Sexp::List(h)) = l.first() {
                    let parts: Vec<&str> = h.iter().filter_map(Sexp::atom).collect();
                    let (x, w) = self.bv(l.get(1).context("indexed operator argument")?)?;
                    return match parts.as_slice() {
                        ["_", "extract", i, j] => {
                            let (i, j): (u32, u32) = (i.parse()?, j.parse()?);
                            Ok((format!("({x}.extractLsb {i} {j})"), Ty::Bv(i - j + 1)))
                        }
                        ["_", "zero_extend", n] => {
                            let n: u32 = n.parse()?;
                            Ok((format!("({x}.zeroExtend {})", w + n), Ty::Bv(w + n)))
                        }
                        ["_", "sign_extend", n] => {
                            let n: u32 = n.parse()?;
                            Ok((format!("({x}.signExtend {})", w + n), Ty::Bv(w + n)))
                        }
                        _ => bail!("unsupported indexed operator {}", Sexp::List(h.clone())),
                    };
                }
                let head = l.first().and_then(Sexp::atom).context("operator")?;
                let args = &l[1..];
                if head == "_" {
                    // (_ bvN w)
                    let v = args
                        .first()
                        .and_then(Sexp::atom)
                        .and_then(|a| a.strip_prefix("bv"));
                    let w = args.get(1).and_then(Sexp::atom);
                    if let (Some(v), Some(w)) = (v, w) {
                        let w: u32 = w.parse()?;
                        return Ok((lit_lean(v, 10, w)?, Ty::Bv(w)));
                    }
                    bail!("unsupported literal");
                }
                let bin = |me: &mut Self, op: &str| -> Result<(String, Ty)> {
                    let (a, w) = me.bv(&args[0])?;
                    let (b, _) = me.bv(&args[1])?;
                    Ok((format!("({a} {op} {b})"), Ty::Bv(w)))
                };
                let method = |me: &mut Self, m: &str| -> Result<(String, Ty)> {
                    let (a, w) = me.bv(&args[0])?;
                    let (b, _) = me.bv(&args[1])?;
                    Ok((format!("({a}.{m} {b})"), Ty::Bv(w)))
                };
                let cmp = |me: &mut Self, op: &str, swap: bool| -> Result<(String, Ty)> {
                    let (a, _) = me.bv(&args[0])?;
                    let (b, _) = me.bv(&args[1])?;
                    let (a, b) = if swap { (b, a) } else { (a, b) };
                    Ok((format!("({a} {op} {b})"), Ty::Bool))
                };
                let scmp = |me: &mut Self, m: &str, swap: bool| -> Result<(String, Ty)> {
                    let (a, _) = me.bv(&args[0])?;
                    let (b, _) = me.bv(&args[1])?;
                    let (a, b) = if swap { (b, a) } else { (a, b) };
                    let op = if m == "slt" { "<" } else { "≤" };
                    Ok((format!("({a}.toInt {op} {b}.toInt)"), Ty::Bool))
                };
                match head {
                    "bvadd" => bin(self, "+"),
                    "bvsub" => bin(self, "-"),
                    "bvmul" => bin(self, "*"),
                    "bvudiv" => bin(self, "/"),
                    "bvurem" => bin(self, "%"),
                    "bvand" => bin(self, "&&&"),
                    "bvor" => bin(self, "|||"),
                    "bvxor" => bin(self, "^^^"),
                    "bvshl" => bin(self, "<<<"),
                    "bvlshr" => bin(self, ">>>"),
                    "bvashr" => method(self, "sshiftRight'"),
                    "bvsdiv" => method(self, "sdiv"),
                    "bvsrem" => method(self, "srem"),
                    "bvneg" => {
                        let (a, w) = self.bv(&args[0])?;
                        Ok((format!("(-{a})"), Ty::Bv(w)))
                    }
                    "bvnot" => {
                        let (a, w) = self.bv(&args[0])?;
                        Ok((format!("(~~~{a})"), Ty::Bv(w)))
                    }
                    "bvult" => cmp(self, "<", false),
                    "bvule" => cmp(self, "≤", false),
                    "bvugt" => cmp(self, "<", true),
                    "bvuge" => cmp(self, "≤", true),
                    "bvslt" => scmp(self, "slt", false),
                    "bvsle" => scmp(self, "sle", false),
                    "bvsgt" => scmp(self, "slt", true),
                    "bvsge" => scmp(self, "sle", true),
                    "=" | "distinct" => {
                        let (a, ta) = self.term(&args[0])?;
                        let (b, _) = self.term(&args[1])?;
                        let op = match (head, ta) {
                            ("=", Ty::Bool) => "↔",
                            ("=", _) => "=",
                            (_, Ty::Bool) => "≠",
                            _ => "≠",
                        };
                        Ok((format!("({a} {op} {b})"), Ty::Bool))
                    }
                    "and" | "or" => {
                        let ps: Vec<String> =
                            args.iter().map(|a| self.prop(a)).collect::<Result<_>>()?;
                        let op = if head == "and" { " ∧ " } else { " ∨ " };
                        Ok((format!("({})", ps.join(op)), Ty::Bool))
                    }
                    "not" => Ok((format!("(¬{})", self.prop(&args[0])?), Ty::Bool)),
                    "=>" => {
                        let a = self.prop(&args[0])?;
                        let b = self.prop(&args[1])?;
                        Ok((format!("({a} → {b})"), Ty::Bool))
                    }
                    "ite" => {
                        let c = self.prop(&args[0])?;
                        let (a, ta) = self.term(&args[1])?;
                        let (b, _) = self.term(&args[2])?;
                        Ok((format!("(if {c} then {a} else {b})"), ta))
                    }
                    "gcd" | "tri" | "popcount" | "fact" => {
                        let xs: Vec<String> = args
                            .iter()
                            .map(|a| self.bv(a).map(|x| x.0))
                            .collect::<Result<_>>()?;
                        if !self.funs_used.iter().any(|f| f == head) {
                            self.funs_used.push(head.to_string());
                        }
                        Ok((format!("({} {})", head, xs.join(" ")), Ty::Bv(64)))
                    }
                    other => bail!("no Lean translation for SMT-LIB operator {other}"),
                }
            }
        }
    }
}

/// Lean definitions of the specification functions (64-bit), as in the SMT
/// prelude of `solve.rs`.
fn lean_fun(f: &str) -> &'static str {
    match f {
        "gcd" => {
            "/-- Euclid's gcd on unsigned values (`gcd a 0 = a`). -/\ndef gcd (a b : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (Nat.gcd a.toNat b.toNat)"
        }
        "tri" => {
            "/-- `0 + 1 + ⋯ + n` modulo `2⁶⁴`. -/\ndef tri (n : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (n.toNat * (n.toNat + 1) / 2)"
        }
        "popcount" => {
            "/-- The number of one bits. -/\ndef popcount (x : BitVec 64) : BitVec 64 := BitVec.ofNat 64 ((List.range 64).countP fun i => x.getLsbD i)"
        }
        "fact" => {
            "/-- The factorial modulo `2⁶⁴`. -/\ndef factN : Nat → Nat\n  | 0 => 1\n  | n + 1 => (n + 1) * factN n\n\ndef fact (n : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (factN n.toNat)"
        }
        _ => "",
    }
}

/// The text of the s-expression starting at byte `start` (balanced parentheses,
/// skipping `;;` comments and strings).
fn sexp_end(src: &str, start: usize) -> Option<usize> {
    let b = src.as_bytes();
    let mut depth = 0i32;
    let mut i = start;
    while i < b.len() {
        match b[i] {
            b';' if b.get(i + 1) == Some(&b';') => {
                while i < b.len() && b[i] != b'\n' {
                    i += 1;
                }
                continue;
            }
            b'"' => {
                i += 1;
                while i < b.len() && b[i] != b'"' {
                    if b[i] == b'\\' {
                        i += 1;
                    }
                    i += 1;
                }
            }
            b'(' => depth += 1,
            b')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i + 1);
                }
            }
            _ => {}
        }
        i += 1;
    }
    None
}

pub struct Generated {
    pub name: String,
    pub lean: String,
}

/// Lean identifier from a problem name.
fn ident(s: &str) -> String {
    let mut out: String = s
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect();
    if let Some(c) = out.get_mut(0..1) {
        c.make_ascii_uppercase();
    }
    out
}

pub fn generate(path: &Path, namespace: &str) -> Result<Generated> {
    let src = std::fs::read_to_string(path)?;
    let p = super::annot::problem_of_wat(path)?;
    let entry = p.entry.clone().context("entry")?;
    let fname = entry.trim_start_matches('$').to_string();
    let start = src
        .find(&format!("(func ${fname} "))
        .or_else(|| src.find(&format!("(func ${fname}\n")))
        .context("function text")?;
    let end = sexp_end(&src, start).context("unbalanced function")?;
    let ftext = &src[start..end];
    if ftext.contains("(call ") || ftext.contains("call $") {
        bail!("outside the wat_spec! fragment: calls");
    }
    if ftext.contains("br_table") {
        bail!("outside the wat_spec! fragment: br_table");
    }
    for c in ["extend", "wrap", "i64.load", "i32.load", "store", "global."] {
        if ftext.contains(c) {
            bail!("outside the wat_spec! fragment: {c}");
        }
    }
    // names and widths: parameters, locals, result
    let parsed = sexp::parse(&strip_comments(ftext))?;
    let items = parsed.list().context("func")?;
    let mut vars: Vec<(String, u32)> = Vec::new();
    let mut header_end = 0usize;
    let mut result_w = None;
    for it in items.iter().skip(2) {
        match it.head() {
            Some("export") => {}
            Some("param") | Some("local") => {
                let l = it.list().unwrap();
                let n = l
                    .get(1)
                    .and_then(Sexp::atom)
                    .context("named params/locals")?;
                let ty = l.get(2).and_then(Sexp::atom).context("type")?;
                let w = match ty {
                    "i32" => 32,
                    "i64" => 64,
                    _ => bail!("type {ty}"),
                };
                let n = n.trim_start_matches('$').to_string();
                vars.push((format!("old_{n}"), w));
                vars.push((n, w));
            }
            Some("result") => {
                let l = it.list().unwrap();
                result_w = Some(match l.get(1).and_then(Sexp::atom) {
                    Some("i32") => 32,
                    _ => 64,
                });
            }
            _ => break,
        }
        header_end += 1;
    }
    if let Some(w) = result_w {
        vars.push(("result".into(), w));
    }
    let mut tr = Tr {
        vars: &vars,
        funs_used: vec![],
    };
    let conj = |tr: &mut Tr, fs: &[String]| -> Result<String> {
        let ps: Vec<String> = fs
            .iter()
            .map(|f| tr.prop(&sexp::parse(&super::exec::old_syntax(f))?))
            .collect::<Result<_>>()?;
        Ok(if ps.is_empty() {
            "True".into()
        } else {
            ps.join(" ∧ ")
        })
    };
    let requires = conj(&mut tr, &p.pre)?;
    let ensures = conj(&mut tr, &p.post)?;
    let mut invs = Vec::new();
    for l in &p.loops {
        invs.push((l.r#loop, conj(&mut tr, std::slice::from_ref(&l.invariant))?));
    }
    // rebuild the function text: header, annotations, body (with invariants)
    let header_items: Vec<String> = items[..2 + header_end]
        .iter()
        .map(|s| s.to_string())
        .collect();
    // `return` becomes a branch out of a block around the body (`wpc`'s body
    // postcondition admits normal completion only)
    let mut body_text = String::new();
    let mut loop_k = 0u32;
    for it in &items[2 + header_end..] {
        body_text.push_str("\n    ");
        body_text.push_str(&with_invariants(it, &invs, &mut loop_k));
    }
    let body_text = match result_w {
        Some(w) => format!("\n  (block $__ret (result i{w}){body_text})"),
        None => format!("\n  (block $__ret{body_text})"),
    };
    let annotated = format!(
        "({} {}\n  (requires {requires})\n  (ensures {ensures}){body_text})",
        header_items[0],
        header_items[1..].join(" ")
    );
    let name = ident(&p.name.clone().unwrap_or(fname.clone()));
    let mut defs = String::new();
    for f in &tr.funs_used {
        defs.push_str(lean_fun(f));
        defs.push_str("\n\n");
    }
    let lean = format!(
        "module\n\npublic import Silmaril.Wasm.WatSpec.Thms\n\n/-!\n# `{fname}` (generated by `wasm-vc lean`)\n\nFrom `{file}`: the annotated function as `wat_spec!`, and its verification\ncondition by `wat_vc` (Silmaril's verified `wpc`). Regenerate; do not edit.\n-/\n\n@[expose] public section\n\nnamespace {namespace}.{name}\n\nopen Silmaril.Wasm.WatSpec\n\n{defs}/-- The problem's function with its specification. -/\ndef spec : Annotated := wat_spec! r#\"\n{annotated}\n\"#\n\ntheorem spec_vc : spec.vc := by\n  wat_vc [spec, BitVec.slt_iff_toInt_lt, BitVec.sle_iff_toInt_le] <;>\n    (try (apply BitVec.eq_of_toInt_eq; omega)) <;> (try bv_omega)\n\nend {namespace}.{name}\n",
        file = path.display(),
    );
    Ok(Generated { name, lean })
}

fn strip_comments(s: &str) -> String {
    s.lines()
        .map(|l| match l.find(";;") {
            Some(i) => &l[..i],
            None => l,
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Print an instruction s-expression, adding `(invariant …)` as the first
/// item of each annotated `loop` (pre-order numbering).
fn with_invariants(s: &Sexp, invs: &[(u32, String)], k: &mut u32) -> String {
    match s {
        Sexp::List(l) if l.first().and_then(Sexp::atom) == Some("loop") => {
            let id = *k;
            *k += 1;
            let mut out = String::from("(loop");
            let mut i = 1;
            if let Some(a) = l.get(1).and_then(Sexp::atom)
                && a.starts_with('$')
            {
                out.push(' ');
                out.push_str(a);
                i = 2;
            }
            if let Some((_, inv)) = invs.iter().find(|(j, _)| *j == id) {
                out.push_str(&format!("\n    (invariant {inv})"));
            }
            for it in &l[i..] {
                out.push_str("\n    ");
                out.push_str(&with_invariants(it, invs, k));
            }
            out.push(')');
            out
        }
        Sexp::List(l) if l.first().and_then(Sexp::atom) == Some("return") => {
            let parts: Vec<String> = l[1..].iter().map(|x| with_invariants(x, invs, k)).collect();
            format!("(br $__ret {})", parts.join(" "))
        }
        Sexp::List(l) => {
            let parts: Vec<String> = l.iter().map(|x| with_invariants(x, invs, k)).collect();
            format!("({})", parts.join(" "))
        }
        Sexp::Atom(a) if a == "return" => "br $__ret".into(),
        other => other.to_string(),
    }
}
