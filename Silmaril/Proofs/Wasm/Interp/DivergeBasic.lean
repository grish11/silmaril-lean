module

public import Silmaril.Wasm.Interp.Diverge.Defs

/-!
# Coinductive divergence of the native semantics: basic facts (proofs)

The recursive semantics is deterministic (`eval_det`), so a problem that
evaluates does not diverge (`eval_not_evalDiv`). The proof is by induction on
the evaluation, unfolding the divergence once at each level. Divergence within
a function is divergence (`localDiv_le_evalDiv`).
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core

variable {H : Type}

theorem eval_det {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r₁ r₂ : Store H × Frame × Flow} (h₁ : Eval s f stk es r₁) (h₂ : Eval s f stk es r₂) :
    r₁ = r₂ := by
  obtain ⟨n₁, e₁⟩ := run_of_eval h₁
  obtain ⟨n₂, e₂⟩ := run_of_eval h₂
  exact Option.some.inj
    ((run_mono (Nat.le_max_left n₁ n₂) e₁).symm.trans (run_mono (Nat.le_max_right n₁ n₂) e₂))

theorem evalDiv_unfold {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr} :
    EvalDiv s f stk es ↔ DivStep EvalDiv EvalDiv s f stk es := by
  have h : divOp (EvalDiv (H := H)) = EvalDiv := (divOp (H := H)).map_gfp
  exact (Eq.to_iff (congrFun (congrFun (congrFun (congrFun h s) f) stk) es)).symm

theorem localDiv_unfold {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr} :
    LocalDiv s f stk es ↔ DivStep LocalDiv ⊥ s f stk es := by
  have h : localDivOp (LocalDiv (H := H)) = LocalDiv := (localDivOp (H := H)).map_gfp
  exact (Eq.to_iff (congrFun (congrFun (congrFun (congrFun h s) f) stk) es)).symm

/-- Coinduction for `EvalDiv`. -/
theorem evalDiv_coind {X : Problem H} (h : ∀ s f stk es, X s f stk es → DivStep X X s f stk es) :
    X ≤ EvalDiv :=
  (divOp (H := H)).le_gfp fun s f stk es hx => h s f stk es hx

/-- Coinduction for `LocalDiv`. -/
theorem localDiv_coind {X : Problem H} (h : ∀ s f stk es, X s f stk es → DivStep X ⊥ s f stk es) :
    X ≤ LocalDiv :=
  (localDivOp (H := H)).le_gfp fun s f stk es hx => h s f stk es hx

/-- Divergence within the function is divergence. -/
theorem localDiv_le_evalDiv : (LocalDiv : Problem H) ≤ EvalDiv :=
  evalDiv_coind fun _ _ _ _ h =>
    (localDiv_unfold.mp h).mono le_rfl (fun _ _ _ _ h => absurd h id)

theorem func_eq {s : Store H} {f : Frame} {x : FuncIdx} {a a' : Nat} {fi fi' : FuncInst H}
    (h : s.func? f x = some (a, fi)) (h' : s.func? f x = some (a', fi')) : a' = a ∧ fi' = fi := by
  have := Option.some.inj (h'.symm.trans h)
  exact ⟨(Prod.mk.inj this).1, (Prod.mk.inj this).2⟩

theorem escapes_blockVals {fl : Flow} {vs : List Val} (h : fl.Escapes) (h' : fl.blockVals = some vs) :
    False := by
  rcases fl with _ | ⟨_ | _, _⟩ | _ | _ | _ <;> simp_all [Flow.Escapes, Flow.blockVals]

/-- **A problem that evaluates does not diverge.** -/
theorem eval_not_evalDiv {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (h : Eval s f stk es r) : ¬ EvalDiv s f stk es := by
  induction h with
  | nil => intro hd; cases evalDiv_unfold.mp hd
  | argsAbort hargs hfl ih =>
    intro hd
    cases evalDiv_unfold.mp hd with
    | args h => exact ih h
    | callee hargs' => cases eval_det hargs' hargs; exact hfl trivial
    | callRet hargs' => cases eval_det hargs' hargs; exact hfl trivial
    | opK _ hargs' => cases eval_det hargs' hargs; exact hfl trivial
  | callOk hargs hfi hcode hty hbody hvs hk iha ihb ihk =>
    intro hd
    cases evalDiv_unfold.mp hd with
    | args h => exact iha h
    | callee hargs' hfi' hcode' hty' h =>
      cases eval_det hargs' hargs
      obtain ⟨rfl, rfl⟩ := func_eq hfi hfi'
      cases FuncCode.wasm.inj (hcode'.symm.trans hcode)
      cases Option.some.inj (hty'.symm.trans hty)
      exact ihb h
    | callRet hargs' hfi' hcode' hty' hbody' hvs' h =>
      cases eval_det hargs' hargs
      obtain ⟨rfl, rfl⟩ := func_eq hfi hfi'
      cases FuncCode.wasm.inj (hcode'.symm.trans hcode)
      cases Option.some.inj (hty'.symm.trans hty)
      cases eval_det hbody' hbody
      cases Option.some.inj (hvs'.symm.trans hvs)
      exact ihk h
    | opK hi => exact hi _ rfl
  | callTrap hargs hfi hcode hty hbody iha ihb =>
    intro hd
    cases evalDiv_unfold.mp hd with
    | args h => exact iha h
    | callee hargs' hfi' hcode' hty' h =>
      cases eval_det hargs' hargs
      obtain ⟨rfl, rfl⟩ := func_eq hfi hfi'
      cases FuncCode.wasm.inj (hcode'.symm.trans hcode)
      cases Option.some.inj (hty'.symm.trans hty)
      exact ihb h
    | callRet hargs' hfi' hcode' hty' hbody' hvs' =>
      cases eval_det hargs' hargs
      obtain ⟨rfl, rfl⟩ := func_eq hfi hfi'
      cases FuncCode.wasm.inj (hcode'.symm.trans hcode)
      cases Option.some.inj (hty'.symm.trans hty)
      cases eval_det hbody' hbody
      cases hvs'
    | opK hi => exact hi _ rfl
  | callThrow hargs hfi hcode hty hbody iha ihb =>
    intro hd
    cases evalDiv_unfold.mp hd with
    | args h => exact iha h
    | callee hargs' hfi' hcode' hty' h =>
      cases eval_det hargs' hargs
      obtain ⟨rfl, rfl⟩ := func_eq hfi hfi'
      cases FuncCode.wasm.inj (hcode'.symm.trans hcode)
      cases Option.some.inj (hty'.symm.trans hty)
      exact ihb h
    | callRet hargs' hfi' hcode' hty' hbody' hvs' =>
      cases eval_det hargs' hargs
      obtain ⟨rfl, rfl⟩ := func_eq hfi hfi'
      cases FuncCode.wasm.inj (hcode'.symm.trans hcode)
      cases Option.some.inj (hty'.symm.trans hty)
      cases eval_det hbody' hbody
      cases hvs'
    | opK hi => exact hi _ rfl
  | opOk hi hargs hflat hk iha ihk =>
    intro hd
    cases evalDiv_unfold.mp hd with
    | args h => exact iha h
    | callee => exact hi _ rfl
    | callRet => exact hi _ rfl
    | opK _ hargs' hflat' h =>
      cases eval_det hargs' hargs
      cases Option.some.inj (hflat'.symm.trans hflat)
      exact ihk h
  | opStop hi hargs hflat hfl iha =>
    intro hd
    cases evalDiv_unfold.mp hd with
    | args h => exact iha h
    | callee => exact hi _ rfl
    | callRet => exact hi _ rfl
    | opK _ hargs' hflat' =>
      cases eval_det hargs' hargs
      cases Option.some.inj (hflat'.symm.trans hflat)
      exact hfl trivial
  | blockOk har hbody hvs hk ihb ihk =>
    intro hd
    cases evalDiv_unfold.mp hd with
    | block har' h => cases Option.some.inj (har'.symm.trans har); exact ihb h
    | blockK har' hbody' hvs' h =>
      cases Option.some.inj (har'.symm.trans har)
      cases eval_det hbody' hbody
      cases Option.some.inj (hvs'.symm.trans hvs)
      exact ihk h
  | blockBrk har hbody ihb =>
    intro hd
    cases evalDiv_unfold.mp hd with
    | block har' h => cases Option.some.inj (har'.symm.trans har); exact ihb h
    | blockK har' hbody' hvs' =>
      cases Option.some.inj (har'.symm.trans har)
      cases eval_det hbody' hbody
      cases hvs'
  | blockEsc har hbody hfl ihb =>
    intro hd
    cases evalDiv_unfold.mp hd with
    | block har' h => cases Option.some.inj (har'.symm.trans har); exact ihb h
    | blockK har' hbody' hvs' =>
      cases Option.some.inj (har'.symm.trans har)
      cases eval_det hbody' hbody
      exact escapes_blockVals hfl hvs'
  | loopOk har hbody hk ihb ihk =>
    intro hd
    cases evalDiv_unfold.mp hd with
    | loop har' h => cases Option.some.inj (har'.symm.trans har); exact ihb h
    | loopK har' hbody' h =>
      cases Option.some.inj (har'.symm.trans har)
      cases eval_det hbody' hbody
      exact ihk h
    | loopBack har' hbody' =>
      cases Option.some.inj (har'.symm.trans har)
      cases eval_det hbody' hbody
  | loopBack har hbody hk ihb ihk =>
    intro hd
    cases evalDiv_unfold.mp hd with
    | loop har' h => cases Option.some.inj (har'.symm.trans har); exact ihb h
    | loopK har' hbody' =>
      cases Option.some.inj (har'.symm.trans har)
      cases eval_det hbody' hbody
    | loopBack har' hbody' h =>
      cases Option.some.inj (har'.symm.trans har)
      cases eval_det hbody' hbody
      exact ihk h
  | loopBrk har hbody ihb =>
    intro hd
    cases evalDiv_unfold.mp hd with
    | loop har' h => cases Option.some.inj (har'.symm.trans har); exact ihb h
    | loopK har' hbody' =>
      cases Option.some.inj (har'.symm.trans har)
      cases eval_det hbody' hbody
    | loopBack har' hbody' =>
      cases Option.some.inj (har'.symm.trans har)
      cases eval_det hbody' hbody
  | loopEsc har hbody hfl ihb =>
    intro hd
    cases evalDiv_unfold.mp hd with
    | loop har' h => cases Option.some.inj (har'.symm.trans har); exact ihb h
    | loopK har' hbody' =>
      cases Option.some.inj (har'.symm.trans har)
      cases eval_det hbody' hbody
      exact hfl
    | loopBack har' hbody' =>
      cases Option.some.inj (har'.symm.trans har)
      cases eval_det hbody' hbody
      exact hfl
  | ifOk hc hb har harm hvs hk ihc iha ihk =>
    intro hd
    cases evalDiv_unfold.mp hd with
    | cond h => exact ihc h
    | arm hc' hb' har' h =>
      cases eval_det hc' hc
      cases Option.some.inj (hb'.symm.trans hb)
      cases Option.some.inj (har'.symm.trans har)
      exact iha h
    | ifK hc' hb' har' harm' hvs' h =>
      cases eval_det hc' hc
      cases Option.some.inj (hb'.symm.trans hb)
      cases Option.some.inj (har'.symm.trans har)
      cases eval_det harm' harm
      cases Option.some.inj (hvs'.symm.trans hvs)
      exact ihk h
  | ifBrk hc hb har harm ihc iha =>
    intro hd
    cases evalDiv_unfold.mp hd with
    | cond h => exact ihc h
    | arm hc' hb' har' h =>
      cases eval_det hc' hc
      cases Option.some.inj (hb'.symm.trans hb)
      cases Option.some.inj (har'.symm.trans har)
      exact iha h
    | ifK hc' hb' har' harm' hvs' =>
      cases eval_det hc' hc
      cases Option.some.inj (hb'.symm.trans hb)
      cases Option.some.inj (har'.symm.trans har)
      cases eval_det harm' harm
      cases hvs'
  | ifEsc hc hb har harm hfl ihc iha =>
    intro hd
    cases evalDiv_unfold.mp hd with
    | cond h => exact ihc h
    | arm hc' hb' har' h =>
      cases eval_det hc' hc
      cases Option.some.inj (hb'.symm.trans hb)
      cases Option.some.inj (har'.symm.trans har)
      exact iha h
    | ifK hc' hb' har' harm' hvs' =>
      cases eval_det hc' hc
      cases Option.some.inj (hb'.symm.trans hb)
      cases Option.some.inj (har'.symm.trans har)
      cases eval_det harm' harm
      exact escapes_blockVals hfl hvs'
  | ifAbort hc hfl ihc =>
    intro hd
    cases evalDiv_unfold.mp hd with
    | cond h => exact ihc h
    | arm hc' => cases eval_det hc' hc; exact hfl trivial
    | ifK hc' => cases eval_det hc' hc; exact hfl trivial

end Silmaril.Wasm.Interp
