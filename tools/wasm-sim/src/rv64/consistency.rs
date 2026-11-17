//! Consistency of a plan's two contract languages on concrete runs: for functions without
//! memory, every returning runtime vector (entry params, results from the simulator) must
//! satisfy `requires ∧ ensures` in SMT-LIB (checked by z3: `(assert (not …))` is unsat) and
//! `Pre ∧ Post` of the generated Lean entry (`#eval decide`, `lake env lean`). Vectors whose
//! SMT terms use declared (uninterpreted) functions are checked on the Lean side only.

use super::reduce::{ABI, Output, Plan};
use std::fmt::Write as _;
use wasmtime::error::{Result, bail};

fn reg_value(r: &str, sig_regs: &[u32], vals: &[u64]) -> Option<u64> {
    sig_regs
        .iter()
        .position(|&x| ABI[x as usize] == r)
        .map(|i| vals[i])
}

/// Replace `(old (reg r))` / `(reg r)` by constants (entry values in requires; in ensures
/// `(reg r)` is the value at return).
fn smt_subst(
    t: &str,
    post: bool,
    ps: &[u32],
    pv: &[u64],
    rs: &[u32],
    rv: &[u64],
) -> Option<String> {
    let mut out = String::new();
    let mut rest = t;
    loop {
        let i_old = rest.find("(old (reg ");
        let i_reg = rest.find("(reg ");
        let (i, old) = match (i_old, i_reg) {
            (Some(a), Some(b)) if a < b => (a, true),
            (_, Some(b)) => (b, false),
            _ => break,
        };
        out.push_str(&rest[..i]);
        let start = i + if old { 10 } else { 5 };
        let end = start + rest[start..].find(')')?;
        let r = rest[start..end].trim();
        let v = if post && !old {
            reg_value(r, rs, rv)?
        } else {
            reg_value(r, ps, pv)?
        };
        write!(out, "#x{v:016x}").ok()?;
        rest = &rest[end + if old { 2 } else { 1 }..];
    }
    out.push_str(rest);
    Some(out)
}

fn lean_subst(t: &str, names: &[(String, u64)]) -> String {
    let mut s = t.to_string();
    for (n, v) in names {
        let mut o = String::new();
        let b = s.as_bytes();
        let mut k = 0;
        while k < s.len() {
            let word = |c: u8| c.is_ascii_alphanumeric() || c == b'_' || c == b'\'' || c == b'.';
            if s[k..].starts_with(n.as_str())
                && (k == 0 || !word(b[k - 1]))
                && b.get(k + n.len()).is_none_or(|&c| !word(c) || c == b'.')
            {
                write!(o, "({v}#64)").unwrap();
                k += n.len();
            } else {
                let ch = s[k..].chars().next().unwrap();
                o.push(ch);
                k += ch.len_utf8();
            }
        }
        s = o;
    }
    s
}

pub fn check(
    plan: &Plan,
    out: &Output,
    runs: &[(String, Vec<u64>, Vec<u64>)],
    lean_dir: Option<&str>,
) -> Result<(u64, u64, u64)> {
    let (mut smt_ok, mut smt_skip, mut lean_ok) = (0, 0, 0);
    let declared: Vec<String> = plan
        .defs
        .iter()
        .filter(|d| d.contains("declare-fun"))
        .filter_map(|d| d.split_whitespace().nth(1).map(String::from))
        .collect();
    let mut lean = String::new();
    let mut lean_n = 0;
    let imports = format!(
        "import Silmaril.Wasm.Logic.Words.Defs\nopen Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Logic.Words\n{}\n",
        plan.lean_prelude
    );
    for (n, pv, rv) in runs {
        let f = plan.functions.iter().find(|f| &f.name == n).unwrap();
        let sig = &out.sigs[n];
        let req = smt_subst(&f.requires, false, &sig.params, pv, &sig.results, rv);
        let ens = smt_subst(&f.ensures, true, &sig.params, pv, &sig.results, rv);
        let (Some(req), Some(ens)) = (req, ens) else {
            bail!("{n}: contract mentions a register that is not a param/result")
        };
        if declared
            .iter()
            .any(|d| ens.contains(&format!("({d} ")) || req.contains(&format!("({d} ")))
        {
            smt_skip += 1;
        } else {
            let script = format!(
                "{}\n(assert (not (and {req} {ens})))\n(check-sat)\n",
                plan.defs.join("\n")
            );
            let o = std::process::Command::new("z3")
                .args(["-in", "-T:10"])
                .stdin(std::process::Stdio::piped())
                .stdout(std::process::Stdio::piped())
                .spawn()
                .and_then(|mut c| {
                    use std::io::Write;
                    c.stdin.take().unwrap().write_all(script.as_bytes())?;
                    c.wait_with_output()
                })?;
            let r = String::from_utf8_lossy(&o.stdout);
            if r.trim() != "unsat" {
                bail!(
                    "{n}: SMT contract false on run params {pv:x?} results {rv:x?}: z3 says {}",
                    r.trim()
                );
            }
            smt_ok += 1;
        }
        if let Some((ent, pre, post)) = &f.lean {
            let mut names: Vec<(String, u64)> = sig
                .params
                .iter()
                .zip(pv)
                .map(|(&r, &v)| (ABI[r as usize].to_string(), v))
                .collect();
            names.extend(
                sig.results
                    .iter()
                    .zip(rv)
                    .map(|(&r, &v)| (format!("r_{}", ABI[r as usize]), v)),
            );
            names.sort_by_key(|x| std::cmp::Reverse(x.0.len()));
            let _ = ent;
            writeln!(
                lean,
                "#eval (\"{n} {lean_n}\", decide (({}) ∧ ({})))",
                lean_subst(pre, &names),
                lean_subst(post, &names)
            )
            .unwrap();
            lean_n += 1;
        }
    }
    if let (Some(dir), true) = (lean_dir, lean_n > 0) {
        let path = std::env::temp_dir().join(format!(
            "rv64-consistency-{}-{}.lean",
            plan.id.replace('/', "_"),
            std::process::id()
        ));
        std::fs::write(&path, format!("{imports}\n{lean}"))?;
        let o = std::process::Command::new("lake")
            .args(["env", "lean"])
            .arg(&path)
            .current_dir(dir)
            .output()?;
        let text =
            String::from_utf8_lossy(&o.stdout).to_string() + &String::from_utf8_lossy(&o.stderr);
        std::fs::remove_file(&path).ok();
        for l in text.lines() {
            if l.contains(", true)") {
                lean_ok += 1;
            } else if l.contains(", false)") || l.contains("error") {
                bail!(
                    "Lean contract check: {l}\n{}",
                    text.lines().take(20).collect::<Vec<_>>().join("\n")
                );
            }
        }
        if lean_ok != lean_n {
            bail!("Lean contract check: {lean_ok}/{lean_n} true\n{text}");
        }
    }
    Ok((smt_ok, smt_skip, lean_ok))
}
