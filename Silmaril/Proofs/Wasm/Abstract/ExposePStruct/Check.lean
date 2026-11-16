module

public import Silmaril.Wasm.Abstract.ExposePStruct.Defs

/-!
Proofs for `Silmaril.Wasm.Abstract.ExposePStruct.Thms`: typed code (`Mor`) is closed under the
syntactic operations of the fragment.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.ExposePStruct

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp Silmaril.Wasm.Abstract.ExposePStruct
open Silmaril.Wasm.Abstract.CallXT (typeArity)

variable {H : Type}

section Chk

variable {ext : ExtArity H} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
  {labels : List Nat}

theorem chkE_none' (es : List BExpr) : chkE ext F mi nl ret labels none es = some none := by
  cases es <;> rfl

theorem chkE_append (oh : Option Nat) (es₁ es₂ : List BExpr) :
    chkE ext F mi nl ret labels oh (es₁ ++ es₂) =
      (chkE ext F mi nl ret labels oh es₁).bind fun o => chkE ext F mi nl ret labels o es₂ := by
  induction es₁ generalizing oh with
  | nil =>
    cases oh with
    | none => rw [chkE_none', chkE_none', Option.bind_some, chkE_none']
    | some h => rfl
  | cons e es₁ ih =>
    cases oh with
    | none => rw [chkE_none', chkE_none', Option.bind_some, chkE_none']
    | some h =>
      simp only [List.cons_append, chkE, Option.bind_assoc]
      congr 1
      funext o
      exact ih o

theorem chkE_singleton (h : Nat) (e : BExpr) :
    chkE ext F mi nl ret labels (some h) [e] = chk1E ext F mi nl ret labels h e := by
  simp only [chkE]
  rcases chk1E ext F mi nl ret labels h e with _ | _ | _ <;> rfl

end Chk

variable {Γ : Ctx H}

theorem mor_single {I : Iface} {o : Option Nat} {e : BExpr} :
    Mor Γ I o [e] ↔
      chk1E (ehExt Γ.tags) Γ.funcs I.env.mi I.env.nl I.env.ret I.env.labels I.h e = some o := by
  unfold Mor chkIn
  rw [chkE_singleton]

theorem mor_comp {I : Iface} {k : Nat} {o : Option Nat} {es₁ es₂ : List BExpr}
    (h₁ : Mor Γ I (some k) es₁) (h₂ : Mor Γ ⟨I.env, k⟩ o es₂) : Mor Γ I o (es₁ ++ es₂) := by
  unfold Mor chkIn at *
  rw [chkE_append, h₁]
  exact h₂

theorem hom_comp {I J K : Iface} {es₁ es₂ : List BExpr} (h₁ : Hom Γ I J es₁)
    (h₂ : Hom Γ J K es₂) : Hom Γ I K (es₁ ++ es₂) := by
  rcases I with ⟨Ie, Ih⟩
  rcases J with ⟨Je, Jh⟩
  obtain ⟨e₁, m₁⟩ := h₁
  obtain ⟨e₂, m₂⟩ := h₂
  dsimp only at e₁ e₂
  subst e₁
  exact ⟨e₂, mor_comp m₁ m₂⟩

theorem mor_stop {I : Iface} {es₁ : List BExpr} (h₁ : Mor Γ I none es₁) (es₂ : List BExpr) :
    Mor Γ I none (es₁ ++ es₂) := by
  unfold Mor chkIn at *
  rw [chkE_append, h₁]
  exact chkE_none' es₂

theorem mor_op {I : Iface} {i : Instr} {args : List BExpr} {h₁ : Nat} {o : Option Nat}
    (ha : Mor Γ I (some h₁) args)
    (hi : flatChkE (ehExt Γ.tags) Γ.funcs I.env.mi I.env.nl I.env.ret I.env.labels h₁ i = some o) :
    Mor Γ I o [.op i args] := by
  rw [mor_single]
  unfold Mor chkIn at ha
  simp only [chk1E, ha, Option.bind_some, hi]

theorem mor_op_stop {I : Iface} {i : Instr} {args : List BExpr} (ha : Mor Γ I none args) :
    Mor Γ I none [.op i args] := by
  rw [mor_single]
  unfold Mor chkIn at ha
  simp only [chk1E, ha, Option.bind_some]

theorem mor_block {I : Iface} {bt : BlockType} {body : List BExpr} {np nr : Nat}
    {o : Option Nat} (hbt : blockArity I.env.mi bt = some (np, nr)) (hle : np ≤ I.h)
    (hb : Mor Γ ⟨I.env.push nr, np⟩ o body) (he : endsAt (some o) nr = true) :
    Mor Γ I (some (I.h - np + nr)) [.block bt body] := by
  rw [mor_single]
  unfold Mor chkIn Env.push at hb
  simp only [chk1E, hbt, hb, he, hle, decide_true, Bool.and_self, ite_true]

theorem mor_loop {I : Iface} {bt : BlockType} {body : List BExpr} {np nr : Nat}
    {o : Option Nat} (hbt : blockArity I.env.mi bt = some (np, nr)) (hle : np ≤ I.h)
    (hb : Mor Γ ⟨I.env.push np, np⟩ o body) (he : endsAt (some o) nr = true) :
    Mor Γ I (some (I.h - np + nr)) [.loop bt body] := by
  rw [mor_single]
  unfold Mor chkIn Env.push at hb
  simp only [chk1E, hbt, hb, he, hle, decide_true, Bool.and_self, ite_true]

theorem mor_if {I : Iface} {bt : BlockType} {c t el : List BExpr} {h₁ np nr : Nat}
    {ot oe : Option Nat} (hc : Mor Γ I (some h₁) c) (hbt : blockArity I.env.mi bt = some (np, nr))
    (hle : np + 1 ≤ h₁) (ht : Mor Γ ⟨I.env.push nr, np⟩ ot t) (het : endsAt (some ot) nr = true)
    (he : Mor Γ ⟨I.env.push nr, np⟩ oe el) (hee : endsAt (some oe) nr = true) :
    Mor Γ I (some (h₁ - 1 - np + nr)) [.if_ bt c t el] := by
  rw [mor_single]
  unfold Mor chkIn at hc
  unfold Mor chkIn Env.push at ht he
  simp only [chk1E, hc, Option.bind_some, hbt, ht, he, het, hee, hle, decide_true,
    Bool.and_self, ite_true]

theorem mor_if_stop {I : Iface} {bt : BlockType} {c t el : List BExpr} (hc : Mor Γ I none c) :
    Mor Γ I none [.if_ bt c t el] := by
  rw [mor_single]
  unfold Mor chkIn at hc
  simp only [chk1E, hc, Option.bind_some]

theorem mor_try {I : Iface} {bt : BlockType} {cs : List Catch} {body : List BExpr}
    {ns : List Nat} {np nr : Nat} {o : Option Nat}
    (hcs : cs.mapM (clauseCount Γ.tags I.env.mi) = some ns)
    (hbt : blockArity I.env.mi bt = some (np, nr)) (hle : np ≤ I.h)
    (hok : catchOk I.env.labels cs ns = true)
    (hb : Mor Γ ⟨I.env.push nr, np⟩ o body) (he : endsAt (some o) nr = true) :
    Mor Γ I (some (I.h - np + nr)) [.tryTable bt cs body] := by
  rw [mor_single]
  unfold Mor chkIn Env.push at hb
  have hx : ehExt (H := H) Γ.tags Γ.funcs I.env.mi (.tryTable bt cs []) = some (.catches ns) := by
    simp only [ehExt, hcs, Option.map_some]
  simp only [chk1E, hx, hbt, hb, he, hle, hok, decide_true, Bool.and_self, ite_true]

/-! ## Flat instructions -/

theorem flat_call {I : Iface} {x : FuncIdx} {p q : Nat}
    (hx : callArity Γ.funcs I.env.mi x = some (p, q)) (hle : p ≤ I.h) :
    flatChkE (ehExt Γ.tags) Γ.funcs I.env.mi I.env.nl I.env.ret I.env.labels I.h (.call x) =
      some (some (I.h - p + q)) := by
  simp only [flatChkE, flatEff, hx, hle, ite_true]

theorem flat_callIndirect {I : Iface} {x : TableIdx} {y : TypeIdx} {p q : Nat}
    (hy : typeArity I.env.mi y = some (p, q)) (hle : p + 1 ≤ I.h) :
    flatChkE (ehExt Γ.tags) Γ.funcs I.env.mi I.env.nl I.env.ret I.env.labels I.h
      (.callIndirect x y) = some (some (I.h - (p + 1) + q)) := by
  simp only [flatChkE, ehExt, tExt, hy, Option.map_some, extStep, hle, ite_true]

theorem flat_callRef {I : Iface} {y : TypeIdx} {p q : Nat}
    (hy : typeArity I.env.mi y = some (p, q)) (hle : p + 1 ≤ I.h) :
    flatChkE (ehExt Γ.tags) Γ.funcs I.env.mi I.env.nl I.env.ret I.env.labels I.h
      (.callRef y) = some (some (I.h - (p + 1) + q)) := by
  simp only [flatChkE, ehExt, tExt, hy, Option.map_some, extStep, hle, ite_true]

theorem flat_returnCall {I : Iface} {x : FuncIdx} {p : Nat}
    (hx : callArity Γ.funcs I.env.mi x = some (p, I.env.ret)) (hle : p ≤ I.h) :
    flatChkE (ehExt Γ.tags) Γ.funcs I.env.mi I.env.nl I.env.ret I.env.labels I.h
      (.returnCall x) = some none := by
  simp only [flatChkE, ehExt, tExt, hx, Option.map_some, extStep, hle, and_self, ite_true]

theorem flat_returnCallIndirect {I : Iface} {x : TableIdx} {y : TypeIdx} {p : Nat}
    (hy : typeArity I.env.mi y = some (p, I.env.ret)) (hle : p + 1 ≤ I.h) :
    flatChkE (ehExt Γ.tags) Γ.funcs I.env.mi I.env.nl I.env.ret I.env.labels I.h
      (.returnCallIndirect x y) = some none := by
  simp only [flatChkE, ehExt, tExt, hy, Option.map_some, extStep, hle, and_self, ite_true]

theorem flat_returnCallRef {I : Iface} {y : TypeIdx} {p : Nat}
    (hy : typeArity I.env.mi y = some (p, I.env.ret)) (hle : p + 1 ≤ I.h) :
    flatChkE (ehExt Γ.tags) Γ.funcs I.env.mi I.env.nl I.env.ret I.env.labels I.h
      (.returnCallRef y) = some none := by
  simp only [flatChkE, ehExt, tExt, hy, Option.map_some, extStep, hle, and_self, ite_true]

theorem flat_throw {I : Iface} {x : TagIdx} {p : Nat}
    (hx : tagFields Γ.tags I.env.mi x = some p) (hle : p ≤ I.h) :
    flatChkE (ehExt Γ.tags) Γ.funcs I.env.mi I.env.nl I.env.ret I.env.labels I.h (.throw x) =
      some none := by
  simp only [flatChkE, ehExt, hx, Option.map_some, extStep, hle, ite_true]

theorem flat_throwRef {I : Iface} (hle : 1 ≤ I.h) :
    flatChkE (ehExt Γ.tags) Γ.funcs I.env.mi I.env.nl I.env.ret I.env.labels I.h .throwRef =
      some none := by
  simp only [flatChkE, ehExt, extStep, hle, ite_true]

theorem flat_br {I : Iface} {l : LabelIdx} {n : Nat} (hl : I.env.labels[l.toNat]? = some n)
    (hle : n ≤ I.h) :
    flatChkE (ehExt Γ.tags) Γ.funcs I.env.mi I.env.nl I.env.ret I.env.labels I.h (.br l) =
      some none := by
  simp only [flatChkE, hl, hle, ite_true]

theorem flat_return {I : Iface} (hle : I.env.ret ≤ I.h) :
    flatChkE (ehExt Γ.tags) Γ.funcs I.env.mi I.env.nl I.env.ret I.env.labels I.h .return_ =
      some none := by
  simp only [flatChkE, hle, ite_true]

/-! ## Typed problems -/

theorem typedP_mor {tags : List TagInst} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} (ht : TypedP tags s f stk es) :
    ∃ (hS : StoreChkE (ehExt tags) s.funcs) (labels : List Nat) (ret : Nat) (o : Option Nat),
      Mor ⟨tags, s.funcs, hS⟩ (ifaceOf f ret labels stk) o es ∧
        Ctx.Good ⟨tags, s.funcs, hS⟩ s := by
  obtain ⟨-, labels, ret, out, hS, hc, -, -, hts⟩ := ht
  exact ⟨hS, labels, ret, out, hc, rfl, hts⟩

end Silmaril.Proofs.Wasm.Abstract.ExposePStruct
