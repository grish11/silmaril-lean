//! Lean output: verification-condition lemmas, candidate tactics, trial files
//! and the proof of the entry's specification for each supported shape.

use crate::term::{B, T};
use crate::vc::{Analysis, Config, Goal, Hyp, Shape, Vc};
use crate::wat::{Bin, Instr, Rel};
use std::collections::BTreeMap;
use std::fmt::Write;

/// Simp lemmas for `wasm_step` in generated proofs.
pub const STEP_LEMMAS: &str = "Idx.toNat, Fin.val_zero, Fin.val_one, Fin.isValue, eqz32, eq32, ne32, \
ltS32, gtS32, leS32, geS32, ltU32, gtU32, leU32, geU32, shrS32, BitVec.toNat_ofNat, Nat.reduceMod, \
Nat.reducePow, Nat.reduceAdd, Nat.reduceLT, ↓reduceIte";

const FRAME_SIMP: &str = "Frame.forCall, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_nil";

pub fn instr(i: &Instr) -> String {
    let list = |c: &[Instr]| code(c);
    match i {
        Instr::LocalGet(x) => format!(".localGet ⟨{x}⟩"),
        Instr::LocalSet(x) => format!(".localSet ⟨{x}⟩"),
        Instr::LocalTee(x) => format!(".localTee ⟨{x}⟩"),
        Instr::Const(c) => format!(".intConst .i32 {c}"),
        Instr::Drop => ".drop".into(),
        Instr::Eqz => ".intTestOp .i32 .eqz".into(),
        Instr::Bin(b) => format!(
            ".intBinOp .i32 {}",
            match b {
                Bin::Add => ".add",
                Bin::Sub => ".sub",
                Bin::Mul => ".mul",
                Bin::And => ".and",
                Bin::Or => ".or",
                Bin::Xor => ".xor",
                Bin::Shl => ".shl",
                Bin::ShrS => "(.shr .signed)",
                Bin::ShrU => "(.shr .unsigned)",
            }
        ),
        Instr::Rel(r) => format!(
            ".intRelOp .i32 {}",
            match r {
                Rel::Eq => ".eq",
                Rel::Ne => ".ne",
                Rel::LtS => "(.lt .signed)",
                Rel::LtU => "(.lt .unsigned)",
                Rel::GtS => "(.gt .signed)",
                Rel::GtU => "(.gt .unsigned)",
                Rel::LeS => "(.le .signed)",
                Rel::LeU => "(.le .unsigned)",
                Rel::GeS => "(.ge .signed)",
                Rel::GeU => "(.ge .unsigned)",
            }
        ),
        Instr::If { result, then, els } => format!(
            ".if_ {} {} {}",
            if *result { "(.value .i32)" } else { ".empty" },
            list(then),
            list(els)
        ),
        Instr::Block { result, body } => format!(
            ".block {} {}",
            if *result { "(.value .i32)" } else { ".empty" },
            list(body)
        ),
        Instr::Loop { result, body } => format!(
            ".loop {} {}",
            if *result { "(.value .i32)" } else { ".empty" },
            list(body)
        ),
        Instr::Br(l) => format!(".br ⟨{l}⟩"),
        Instr::BrIf(l) => format!(".brIf ⟨{l}⟩"),
        Instr::Call(f) => format!(".call ⟨{f}⟩"),
    }
}

pub fn code(c: &[Instr]) -> String {
    format!("[{}]", c.iter().map(instr).collect::<Vec<_>>().join(", "))
}

pub fn goal(g: &Goal, funs: &BTreeMap<String, String>) -> String {
    match g {
        Goal::Prop(b) => b.lean(funs),
        Goal::Eq(l, r) => format!("{} = {}", l.lean(funs), r.lean(funs)),
        Goal::Lt(a, b) => format!("{}.toNat < {}.toNat", a.lean(funs), b.lean(funs)),
    }
}

pub fn hyp(h: &Hyp, funs: &BTreeMap<String, String>) -> String {
    match h {
        Hyp::Cond(b, true) => format!("{} = true", b.lean_bool(funs)),
        Hyp::Cond(b, false) => format!("¬({} = true)", b.lean_bool(funs)),
        Hyp::Inv(b) => b.lean(funs),
    }
}

/// `(v₁ v₂ : BitVec 32) (hc : …) (hi : …) : goal`.
pub fn signature(vc: &Vc, funs: &BTreeMap<String, String>) -> String {
    let mut s = String::new();
    if !vc.vars.is_empty() {
        write!(s, "({} : BitVec 32)", vc.vars.join(" ")).unwrap();
    }
    for (n, h) in &vc.hyps {
        write!(s, " ({n} : {})", hyp(h, funs)).unwrap();
    }
    write!(s, " :\n    {}", goal(&vc.goal, funs)).unwrap();
    s
}

/// A preparation step turning an equality condition into a usable fact.
fn prep(vc: &Vc, funs: &BTreeMap<String, String>) -> Option<String> {
    vc.hyps.iter().find_map(|(_, h)| match h {
        Hyp::Cond(B::Cmp(op, a, b), true) if op == "=" => match &**a {
            T::Var(x) if !mentions(b, x) => Some(format!(
                "have h0 : {x} = {} := by simpa using hc\n  subst h0",
                b.lean(funs)
            )),
            _ => Some(format!(
                "have h0 : {} = {} := by simpa using hc",
                a.lean(funs),
                b.lean(funs)
            )),
        },
        Hyp::Cond(B::Cmp(op, a, b), false) if op == "=" => Some(format!(
            "have h0 : {} ≠ {} := by simpa using hc",
            a.lean(funs),
            b.lean(funs)
        )),
        _ => None,
    })
}

fn mentions(t: &T, x: &str) -> bool {
    let mut v = Vec::new();
    t.vars(&mut v);
    v.iter().any(|y| y == x)
}

/// Candidate tactic scripts for a condition, cheapest first. `hints` are the
/// Lean texts of the hints the solver's unsat core used (or all hints).
pub fn candidates(vc: &Vc, cfg: &Config, hints: &[String]) -> Vec<String> {
    let funs = cfg.lean_names();
    let mut out = vec!["bv_omega".to_string(), "simp_all".to_string()];
    let p = prep(vc, &funs);
    if let Some(p) = &p {
        out.push(format!("{p}\n  bv_omega"));
        out.push(format!("{p}\n  simp_all"));
    }
    // Instantiate each hint's `{v}` with each variable; combine all hints.
    let mut combos: Vec<Vec<String>> = vec![vec![]];
    for h in hints {
        let insts: Vec<String> = if h.contains("{v}") {
            vc.vars.iter().map(|v| h.replace("{v}", v)).collect()
        } else {
            vec![h.clone()]
        };
        let mut next = Vec::new();
        for c in &combos {
            for i in &insts {
                let mut c = c.clone();
                c.push(i.clone());
                next.push(c);
            }
        }
        combos = next;
        combos.truncate(32);
    }
    for c in combos.iter().filter(|c| !c.is_empty()) {
        let body = c.join("\n  ");
        out.push(format!("{body}\n  bv_omega"));
        if let Some(p) = &p {
            out.push(format!("{p}\n  {body}\n  bv_omega"));
        }
    }
    out
}

pub struct Header<'a> {
    pub cfg: &'a Config,
    pub namespace: String,
    pub sub: &'a str,
    pub module: bool,
    pub doc: String,
}

pub fn header(h: &Header) -> String {
    let mut s = String::new();
    let ns = &h.namespace;
    let (kw, imp) = if h.module {
        ("module\n\n", "public import")
    } else {
        ("", "import")
    };
    write!(
        s,
        "{kw}{imp} {ns}.Defs\n{imp} Silmaril.WasmSpec.Common.Thms\n"
    )
    .unwrap();
    for i in &h.cfg.imports {
        writeln!(s, "{imp} {i}").unwrap();
    }
    // The tactics (`wasm_step`, `vc_tactic`) the generated proofs use.
    s.push_str("import Silmaril.Wasm.Logic.Tactic.Defs\n");
    write!(s, "\n/-!\n{}\n-/\n\n", h.doc).unwrap();
    if h.module {
        s.push_str("@[expose] public section\n\n");
    }
    s.push_str(
        "set_option linter.unusedVariables false\nset_option linter.unusedSimpArgs false\n\n",
    );
    write!(
        s,
        "namespace {ns}.{}\n\nopen Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics \
         Silmaril.Wasm.Logic.Core\n  Silmaril.WasmSpec Silmaril.WasmSpec.Ops {ns}\n\n",
        h.sub
    )
    .unwrap();
    s
}

/// A trial file: each candidate of each condition as an `example`. Returns the
/// text and, per (condition, candidate), its line range.
pub fn trial(
    h: &Header,
    a: &Analysis,
    cands: &[Vec<String>],
) -> (String, Vec<(usize, usize, usize, usize)>) {
    let funs = h.cfg.lean_names();
    let mut s = header(h);
    let mut ranges = Vec::new();
    for (i, vc) in a.vcs.iter().enumerate() {
        for (j, c) in cands[i].iter().enumerate() {
            let start = s.lines().count() + 1;
            write!(
                s,
                "-- {} candidate {j}\nset_option maxHeartbeats 400000 in\nexample {} := by\n  {}\n\n",
                vc.name,
                signature(vc, &funs),
                c
            )
            .unwrap();
            let end = s.lines().count();
            ranges.push((i, j, start, end));
        }
    }
    writeln!(s, "end {}.{}", h.namespace, h.sub).unwrap();
    (s, ranges)
}

fn args_list(a: &Analysis) -> String {
    format!(
        "[{}]",
        a.params0
            .iter()
            .map(|p| format!(".i32 {p}"))
            .collect::<Vec<_>>()
            .join(", ")
    )
}

fn local_types(a: &Analysis) -> String {
    format!(
        "[{}]",
        a.func
            .locals
            .iter()
            .map(|_| ".i32")
            .collect::<Vec<_>>()
            .join(", ")
    )
}

/// The whole solution module: conditions with their chosen tactics, then the
/// proof of the specification.
pub fn solution(h: &Header, a: &Analysis, tactics: &[String], theorem: &str) -> String {
    let cfg = h.cfg;
    let funs = cfg.lean_names();
    let mut s = header(h);
    let lf = &cfg.lean_func;
    writeln!(
        s,
        "/-- The quoted body. -/\ntheorem body_eq : {lf}.body =\n    {} := rfl\n",
        code(&a.func.body)
    )
    .unwrap();
    for (vc, t) in a.vcs.iter().zip(tactics) {
        writeln!(
            s,
            "theorem {} {} := by\n  {}\n",
            vc.name,
            signature(vc, &funs),
            t
        )
        .unwrap();
    }
    let p0 = a.params0.join(" ");
    let lemmas = STEP_LEMMAS;
    let show_frame = format!("Frame.forCall m {} {}", args_list(a), local_types(a));
    let ret = |vc: &str, args: &str| format!("congrArg (fun v => [Val.i32 v]) ({vc} {args})");
    match &a.shape {
        Shape::Straight { body } => {
            write!(
                s,
                "/-- The specification: symbolic execution, then `vc_post`. -/\ntheorem {theorem} : {spec} := by\n  intro {p0} H P host s m\n  show WP P host s ({show_frame}) (expression {}) _\n  simp only [{FRAME_SIMP}]\n  wasm_step [{lemmas}]\n  exact (⟨rfl, rfl, {}⟩ : _ ∧ _ ∧ _)\n\n",
                code(body),
                ret("vc_post", &p0),
                spec = cfg.spec,
            )
            .unwrap();
        }
        Shape::Branch {
            pre,
            cond,
            then,
            els,
        } => {
            let c = cond.lean_bool(&funs);
            let (t, e) = (
                format!("({} : List Instr)", code(then)),
                format!("({} : List Instr)", code(els)),
            );
            let branch = |rw: &str, vc: &str| {
                format!(
                    "  · rw [{rw}]\n    wasm_block\n    wasm_step [{lemmas}]\n    simp only [blockPost, seqPost]\n    exact wp_vals (vs := [_]) ⟨rfl, rfl, {}⟩\n",
                    ret(vc, &format!("{p0} hc"))
                )
            };
            write!(
                s,
                "/-- The specification: symbolic execution, one case per branch. -/\ntheorem {theorem} : {spec} := by\n  intro {p0} H P host s m\n  show WP P host s ({show_frame})\n    (expression {} ++ .plain (.if_ (.value .i32) {t} {e}) :: []) _\n  simp only [{FRAME_SIMP}]\n  wasm_step [{lemmas}]\n  refine wp_if_bool32_cons (vs := []) (rest := []) ?_\n  by_cases hc : {c} = true\n{}{}\n",
                code(pre),
                branch(&format!("ite_eq_left_of_eq_true {t} {e} (eq_true hc)"), "vc_then"),
                branch(&format!("ite_eq_right_of_eq_false {t} {e} (eq_false hc)"), "vc_else"),
                spec = cfg.spec,
            )
            .unwrap();
        }
        Shape::Loop {
            p1,
            cond,
            p2,
            post,
            inv,
            measure,
            next,
        } => {
            let ls = a.locals.join(" ");
            let frame_of = |m: &str| {
                format!(
                    "⟨[{}], {m}⟩",
                    a.locals
                        .iter()
                        .map(|l| format!("some (.i32 {l})"))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            };
            let frame = frame_of("m");
            let typed0 = if a.params0.is_empty() {
                String::new()
            } else {
                format!("({p0} : BitVec 32)")
            };
            write!(
                s,
                "/-- The loop invariant (from the annotations or a proposal), with the\nmeasure as the loop rule's index. -/\ndef inv {{H : Type}} (s₀ : Store H) (m : ModuleInst) {typed0} :\n    Nat → Store H → Frame → List Val → Prop := fun k s f vs =>\n  s = s₀ ∧ vs = [] ∧ ∃ {ls} : BitVec 32,\n    f = {frame} ∧ k = {}.toNat ∧ ({})\n\n",
                measure.lean(&funs),
                inv.lean(&funs)
            )
            .unwrap();
            let mut lb = p1.clone();
            lb.push(Instr::BrIf(1));
            lb.extend(p2.iter().cloned());
            lb.push(Instr::Br(0));
            let init: Vec<String> = a
                .params0
                .iter()
                .cloned()
                .chain(a.func.locals.iter().map(|_| "(0 : BitVec 32)".to_string()))
                .collect();
            let nexts: Vec<String> = next.iter().map(|t| t.lean(&funs)).collect();
            let all = format!("{p0} {ls}");
            let mut p2br = p2.clone();
            p2br.push(Instr::Br(0));
            let c = cond.lean_bool(&funs);
            let res = format!("[.i32 {}]", a.ensures.lean(&funs));
            write!(
                s,
                "variable {{H : Type}} {{P : Profile}} {{host : HostSemantics H}}\n\n\
/-- What the loop body must establish at measure `k`. -/\n\
abbrev loopQ (s₀ : Store H) (m : ModuleInst) {typed0} (k : Nat) : Post H :=\n  \
loopPost 0 (inv s₀ m {p0}) k (seqPost P host [] (blockPost 0\n    \
(seqPost P host (expression {post}) (funcPost P host 1 fun s' r => s' = s₀ ∧ r = {res}))))\n\n\
/-- The exit branch: `POST` returns the specified result (`vc_exit`). -/\n\
theorem loop_exit {{s₀ : Store H}} {{m : ModuleInst}} {{{all} : BitVec 32}}\n    \
(hc : {c} = true) (hi : {invl}) :\n    \
loopQ (P := P) (host := host) s₀ m {p0} {meas} s₀ {frame} (.br 1 []) := by\n  \
refine ⟨[], [], rfl, rfl, ?_⟩\n  \
show WP P host s₀ _ (vals [] ++ expression {post}) _\n  \
wasm_step [{lemmas}]\n  \
exact (⟨rfl, rfl, {exit}⟩ : _ ∧ _ ∧ _)\n\n\
/-- The iteration: the state after `P2` satisfies the invariant at a smaller\nmeasure (`vc_step`, `vc_dec`). -/\n\
theorem loop_next {{s₀ : Store H}} {{m : ModuleInst}} {{{all} : BitVec 32}}\n    \
(hc : ¬({c} = true)) (hi : {invl}) :\n    \
WP P host s₀ {frame} (vals [] ++ expression {p2br})\n      \
(loopQ (P := P) (host := host) s₀ m {p0} {meas}) := by\n  \
show WP P host s₀ _ (vals [] ++ expression {p2} ++ .plain (.br ⟨0⟩) :: []) _\n  \
wasm_step [{lemmas}]\n  \
exact wp_br (rest := []) ⟨[], [], _, rfl, rfl, vc_dec {all} hc hi, rfl, rfl,\n    \
{nexts}, rfl, rfl, vc_step {all} hc hi⟩\n\n\
/-- The loop body, from the invariant: one case per value of the exit test. -/\n\
theorem loop_body {{s₀ : Store H}} {{m : ModuleInst}} {typed0b} {{k : Nat}} {{s : Store H}}\n    \
{{f : Frame}} {{vs : List Val}} (h : inv s₀ m {p0} k s f vs) :\n    \
WP P host s f (vals vs ++ expression {lbc}) (loopQ (P := P) (host := host) s₀ m {p0} k) := by\n  \
obtain ⟨rfl, rfl, {lsc}, rfl, rfl, hi⟩ := h\n  \
show WP P host s _ (vals [] ++ expression {p1c} ++ .plain (.brIf ⟨1⟩) ::\n    expression {p2bc}) _\n  \
wasm_step [{lemmas}]\n  \
refine wp_brIf_bool32 (vs := []) ?_\n  \
by_cases hc : {c} = true\n  \
· exact Eq.mpr (ite_eq_left_of_eq_true _ _ (eq_true hc)) (loop_exit hc hi)\n  \
· exact Eq.mpr (ite_eq_right_of_eq_false _ _ (eq_false hc)) (loop_next hc hi)\n\n\
/-- The specification: the loop rule with `inv` and `loop_body`. -/\n\
theorem {theorem} : {spec} := by\n  \
intro {p0} H P host s m\n  \
show WP P host s ({show_frame})\n    \
([] ++ .plain (.block .empty [.loop .empty {lbc}]) :: expression {post}) _\n  \
simp only [{FRAME_SIMP}]\n  \
refine wp_block_cons (vs := []) (t₁ := []) (t₂ := []) rfl rfl ?_\n  \
refine wp_loop_cons (vs := []) (rest := []) (t₁ := []) (t₂ := []) (inv s m {p0}) ?_\n    \
(fun _ _ _ _ h => loop_body h) ⟨rfl, rfl, {initw}, rfl, rfl, vc_init {p0}⟩\n  \
rintro k s' f vs ⟨-, rfl, -⟩\n  \
exact ⟨rfl, rfl⟩\n\n",
                post = code(post),
                invl = inv.lean(&funs),
                meas = format!("{}.toNat", measure.lean(&funs)),
                exit = ret("vc_exit", &format!("{all} hc hi")),
                p2br = code(&p2br),
                p2 = code(p2),
                nexts = nexts.join(", "),
                typed0b = if a.params0.is_empty() { String::new() } else { format!("{{{p0} : BitVec 32}}") },
                lbc = code(&lb),
                lsc = a.locals.join(", "),
                p1c = code(p1),
                p2bc = code(&p2br),
                initw = init.join(", "),
                spec = cfg.spec,
            )
            .unwrap();
        }
    }
    writeln!(s, "end {}.{}", h.namespace, h.sub).unwrap();
    s
}
