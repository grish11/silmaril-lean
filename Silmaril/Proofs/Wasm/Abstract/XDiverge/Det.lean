module

public import Silmaril.Proofs.Wasm.Abstract.XDiverge.Basic
public import Silmaril.Proofs.Wasm.Abstract.CallX.Expose

/-!
Proofs for `Silmaril.Wasm.Abstract.XDiverge.Thms`: determinism.

`evalOX_det`: two `EvalOX` runs of the same problem, under oracles that answer
every call alike (`Agree`), end alike. The induction follows the rules; every
callee resolution is unique (`CallRes.indRes_unique`, `CallX.tailRes_unique`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.XDiverge

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel)
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.XRecursion
open Silmaril.Proofs.Wasm.Abstract.CallX (addr_val_inj tailRes_unique notX_of_flat)

variable {H : Type}

/-- Two oracles answer every call alike. -/
def Agree (C₁ C₂ : CallRel H) : Prop :=
  ∀ s a args o₁ o₂, C₁ s a args o₁ → C₂ s a args o₂ → o₁ = o₂

theorem nn {s₁ s₁' : Store H} {f₁ f₁' : Frame} {fl : Flow} {stk : List Val}
    (hfl : ¬ fl.IsNormal) (h : (s₁, f₁, fl) = (s₁', f₁', Flow.normal stk)) : False := by
  cases h; exact hfl trivial

theorem nrm {s₁ s₁' : Store H} {f₁ f₁' : Frame} {x x' : List Val}
    (h : (s₁, f₁, Flow.normal x) = (s₁', f₁', Flow.normal x')) : s₁ = s₁' ∧ f₁ = f₁' ∧ x = x' := by
  cases h; exact ⟨rfl, rfl, rfl⟩

theorem nrmI {s₁ s₁' : Store H} {f₁ f₁' : Frame} {stk₁ stk₁' : List Val} {ad ad' : AddrType}
    {i : BitVec ad.intType.width} {i' : BitVec ad'.intType.width}
    (h : (s₁, f₁, Flow.normal (Val.num ⟨.int ad.intType, i⟩ :: stk₁)) =
      (s₁', f₁', Flow.normal (Val.num ⟨.int ad'.intType, i'⟩ :: stk₁'))) :
    s₁ = s₁' ∧ f₁ = f₁' ∧ ∃ e : ad = ad', e ▸ i = i' ∧ stk₁ = stk₁' := by
  obtain ⟨h1, h2, h3⟩ := nrm h
  exact ⟨h1, h2, addr_val_inj h3⟩

theorem func?_det {s : Store H} {f : Frame} {x : FuncIdx} {a a' : Nat} {fi fi' : FuncInst H}
    (h : s.func? f x = some (a, fi)) (h' : s.func? f x = some (a', fi')) : a = a' ∧ fi = fi' := by
  rw [h] at h'; cases h'; exact ⟨rfl, rfl⟩

theorem some_det {α : Type _} {o : Option α} {a a' : α} (h : o = some a) (h' : o = some a') :
    a = a' := by rw [h] at h'; cases h'; rfl

theorem not_abrupt_of_retVals {fl : Flow} {vs : List Val} (h : fl.retVals = some vs) :
    ¬ fl.Abrupt := by
  cases fl <;> simp_all [Flow.retVals, Flow.Abrupt]

theorem retVals_trap {vs : List Val} (h : Flow.trap.retVals = some vs) : False := by
  simp [Flow.retVals] at h

theorem retVals_throw {vs : List Val} {t : Nat} (h : (Flow.throw t).retVals = some vs) : False := by
  simp [Flow.retVals] at h

theorem blockVals_esc {fl : Flow} {vs : List Val} (h : fl.blockVals = some vs) : ¬ fl.Escapes := by
  cases fl with
  | brk k _ => cases k <;> simp_all [Flow.blockVals, Flow.Escapes]
  | _ => simp_all [Flow.blockVals, Flow.Escapes]

theorem blockVals_brk {k : Nat} {ws vs : List Val} (h : (Flow.brk (k + 1) ws).blockVals = some vs) :
    False := by simp [Flow.blockVals] at h

theorem esc_brk {k : Nat} {ws : List Val} (h : (Flow.brk k ws).Escapes) : False := h

theorem esc_normal {ws : List Val} (h : (Flow.normal ws).Escapes) : False := h

theorem flat_x {s : Store H} {f : Frame} {stk : List Val} {i : Instr}
    {r : Store H × Frame × Flow} (h : evalFlat s f stk i = some r) (hx : isXCall i = true) : False := by
  rw [notX_of_flat h] at hx; cases hx

/-- **Determinism.** Under oracles that answer alike, `EvalOX` runs of the same
problem end alike. -/
theorem evalOX_det {C₁ C₂ : CallRel H} (hC : Agree C₁ C₂) {s : Store H} {f : Frame}
    {stk : List Val} {es : List BExpr} {r₁ : Store H × Frame × Flow}
    (h₁ : EvalOX C₁ s f stk es r₁) : ∀ {r₂}, EvalOX C₂ s f stk es r₂ → r₁ = r₂ := by
  induction h₁ with
  | nil => intro r₂ h₂; cases h₂; rfl
  | argsAbort hargs hfl ih =>
    intro r₂ h₂
    cases h₂ with
    | argsAbort hargs' _ => exact ih hargs'
    | callOk hargs' => exact (nn hfl (ih hargs')).elim
    | callTrap hargs' => exact (nn hfl (ih hargs')).elim
    | callThrow hargs' => exact (nn hfl (ih hargs')).elim
    | opOk _ hargs' => exact (nn hfl (ih hargs')).elim
    | opStop _ hargs' => exact (nn hfl (ih hargs')).elim
    | callIndOk hargs' => exact (nn hfl (ih hargs')).elim
    | callIndRes hargs' => exact (nn hfl (ih hargs')).elim
    | callIndStop hargs' => exact (nn hfl (ih hargs')).elim
    | callRefOk hargs' => exact (nn hfl (ih hargs')).elim
    | callRefNull hargs' => exact (nn hfl (ih hargs')).elim
    | callRefStop hargs' => exact (nn hfl (ih hargs')).elim
    | tail hargs' => exact (nn hfl (ih hargs')).elim
    | tailRes hargs' => exact (nn hfl (ih hargs')).elim
  | callOk hargs hfi hty hcall hvs hk iha ihk =>
    intro r₂ h₂
    cases h₂ with
    | argsAbort hargs' hfl' => exact (nn hfl' (iha hargs').symm).elim
    | callOk hargs' hfi' hty' hcall' hvs' hk' =>
      obtain ⟨rfl, rfl, rfl⟩ := nrm (iha hargs')
      obtain ⟨rfl, rfl⟩ := func?_det hfi hfi'
      cases some_det hty hty'
      cases hC _ _ _ _ _ hcall hcall'
      cases some_det hvs hvs'
      exact ihk hk'
    | callTrap hargs' hfi' hty' hcall' =>
      obtain ⟨rfl, rfl, rfl⟩ := nrm (iha hargs')
      obtain ⟨rfl, rfl⟩ := func?_det hfi hfi'
      cases some_det hty hty'
      cases hC _ _ _ _ _ hcall hcall'
      exact (retVals_trap hvs).elim
    | callThrow hargs' hfi' hty' hcall' =>
      obtain ⟨rfl, rfl, rfl⟩ := nrm (iha hargs')
      obtain ⟨rfl, rfl⟩ := func?_det hfi hfi'
      cases some_det hty hty'
      cases hC _ _ _ _ _ hcall hcall'
      exact (retVals_throw hvs).elim
    | opOk hi => exact (hi _ rfl).elim
    | opStop hi => exact (hi _ rfl).elim
    | tail _ hres => cases hres
    | tailRes _ hres => cases hres
  | callTrap hargs hfi hty hcall iha =>
    intro r₂ h₂
    cases h₂ with
    | argsAbort hargs' hfl' => exact (nn hfl' (iha hargs').symm).elim
    | callOk hargs' hfi' hty' hcall' hvs' =>
      obtain ⟨rfl, rfl, rfl⟩ := nrm (iha hargs')
      obtain ⟨rfl, rfl⟩ := func?_det hfi hfi'
      cases some_det hty hty'
      cases hC _ _ _ _ _ hcall hcall'
      exact (retVals_trap hvs').elim
    | callTrap hargs' hfi' hty' hcall' =>
      obtain ⟨rfl, rfl, rfl⟩ := nrm (iha hargs')
      obtain ⟨rfl, rfl⟩ := func?_det hfi hfi'
      cases some_det hty hty'
      cases hC _ _ _ _ _ hcall hcall'
      rfl
    | callThrow hargs' hfi' hty' hcall' =>
      obtain ⟨rfl, rfl, rfl⟩ := nrm (iha hargs')
      obtain ⟨rfl, rfl⟩ := func?_det hfi hfi'
      cases some_det hty hty'
      cases hC _ _ _ _ _ hcall hcall'
    | opOk hi => exact (hi _ rfl).elim
    | opStop hi => exact (hi _ rfl).elim
    | tail _ hres => cases hres
    | tailRes _ hres => cases hres
  | callThrow hargs hfi hty hcall iha =>
    intro r₂ h₂
    cases h₂ with
    | argsAbort hargs' hfl' => exact (nn hfl' (iha hargs').symm).elim
    | callOk hargs' hfi' hty' hcall' hvs' =>
      obtain ⟨rfl, rfl, rfl⟩ := nrm (iha hargs')
      obtain ⟨rfl, rfl⟩ := func?_det hfi hfi'
      cases some_det hty hty'
      cases hC _ _ _ _ _ hcall hcall'
      exact (retVals_throw hvs').elim
    | callTrap hargs' hfi' hty' hcall' =>
      obtain ⟨rfl, rfl, rfl⟩ := nrm (iha hargs')
      obtain ⟨rfl, rfl⟩ := func?_det hfi hfi'
      cases some_det hty hty'
      cases hC _ _ _ _ _ hcall hcall'
    | callThrow hargs' hfi' hty' hcall' =>
      obtain ⟨rfl, rfl, rfl⟩ := nrm (iha hargs')
      obtain ⟨rfl, rfl⟩ := func?_det hfi hfi'
      cases some_det hty hty'
      cases hC _ _ _ _ _ hcall hcall'
      rfl
    | opOk hi => exact (hi _ rfl).elim
    | opStop hi => exact (hi _ rfl).elim
    | tail _ hres => cases hres
    | tailRes _ hres => cases hres
  | opOk hi hargs hflat hk iha ihk =>
    intro r₂ h₂
    cases h₂ with
    | argsAbort hargs' hfl' => exact (nn hfl' (iha hargs').symm).elim
    | callOk => exact (hi _ rfl).elim
    | callTrap => exact (hi _ rfl).elim
    | callThrow => exact (hi _ rfl).elim
    | opOk _ hargs' hflat' hk' =>
      obtain ⟨rfl, rfl, rfl⟩ := nrm (iha hargs')
      cases some_det hflat hflat'
      exact ihk hk'
    | opStop _ hargs' hflat' hfl' =>
      obtain ⟨rfl, rfl, rfl⟩ := nrm (iha hargs')
      cases some_det hflat hflat'
      exact (hfl' trivial).elim
    | callIndOk => exact (flat_x hflat rfl).elim
    | callIndRes => exact (flat_x hflat rfl).elim
    | callIndStop => exact (flat_x hflat rfl).elim
    | callRefOk => exact (flat_x hflat rfl).elim
    | callRefNull => exact (flat_x hflat rfl).elim
    | callRefStop => exact (flat_x hflat rfl).elim
    | tail _ hres => exact (flat_x hflat (isXCall_of_tailRes hres)).elim
    | tailRes _ hres => exact (flat_x hflat (isXCall_of_tailRes hres)).elim
  | opStop hi hargs hflat hfl iha =>
    intro r₂ h₂
    cases h₂ with
    | argsAbort hargs' hfl' => exact (nn hfl' (iha hargs').symm).elim
    | callOk => exact (hi _ rfl).elim
    | callTrap => exact (hi _ rfl).elim
    | callThrow => exact (hi _ rfl).elim
    | opOk _ hargs' hflat' =>
      obtain ⟨rfl, rfl, rfl⟩ := nrm (iha hargs')
      cases some_det hflat hflat'
      exact (hfl trivial).elim
    | opStop _ hargs' hflat' =>
      obtain ⟨rfl, rfl, rfl⟩ := nrm (iha hargs')
      exact some_det hflat hflat'
    | callIndOk => exact (flat_x hflat rfl).elim
    | callIndRes => exact (flat_x hflat rfl).elim
    | callIndStop => exact (flat_x hflat rfl).elim
    | callRefOk => exact (flat_x hflat rfl).elim
    | callRefNull => exact (flat_x hflat rfl).elim
    | callRefStop => exact (flat_x hflat rfl).elim
    | tail _ hres => exact (flat_x hflat (isXCall_of_tailRes hres)).elim
    | tailRes _ hres => exact (flat_x hflat (isXCall_of_tailRes hres)).elim
  | blockOk har hbody hvs hk ihb ihk =>
    intro r₂ h₂
    cases h₂ with
    | blockOk har' hbody' hvs' hk' =>
      cases some_det har har'
      cases ihb hbody'
      cases some_det hvs hvs'
      exact ihk hk'
    | blockBrk har' hbody' =>
      cases some_det har har'
      cases ihb hbody'
      exact (blockVals_brk hvs).elim
    | blockEsc har' hbody' hfl' =>
      cases some_det har har'
      cases ihb hbody'
      exact (blockVals_esc hvs hfl').elim
  | blockBrk har hbody ihb =>
    intro r₂ h₂
    cases h₂ with
    | blockOk har' hbody' hvs' =>
      cases some_det har har'
      cases ihb hbody'
      exact (blockVals_brk hvs').elim
    | blockBrk har' hbody' =>
      cases some_det har har'
      cases ihb hbody'
      rfl
    | blockEsc har' hbody' hfl' =>
      cases some_det har har'
      cases ihb hbody'
      exact (esc_brk hfl').elim
  | blockEsc har hbody hfl ihb =>
    intro r₂ h₂
    cases h₂ with
    | blockOk har' hbody' hvs' =>
      cases some_det har har'
      cases ihb hbody'
      exact (blockVals_esc hvs' hfl).elim
    | blockBrk har' hbody' =>
      cases some_det har har'
      cases ihb hbody'
      exact (esc_brk hfl).elim
    | blockEsc har' hbody' =>
      cases some_det har har'
      exact ihb hbody'
  | loopOk har hbody hk ihb ihk =>
    intro r₂ h₂
    cases h₂ with
    | loopOk har' hbody' hk' =>
      cases some_det har har'
      cases ihb hbody'
      exact ihk hk'
    | loopBack har' hbody' => cases some_det har har'; cases ihb hbody'
    | loopBrk har' hbody' => cases some_det har har'; cases ihb hbody'
    | loopEsc har' hbody' hfl' =>
      cases some_det har har'
      cases ihb hbody'
      exact (esc_normal hfl').elim
  | loopBack har hbody hk ihb ihk =>
    intro r₂ h₂
    cases h₂ with
    | loopOk har' hbody' => cases some_det har har'; cases ihb hbody'
    | loopBack har' hbody' hk' =>
      cases some_det har har'
      cases ihb hbody'
      exact ihk hk'
    | loopBrk har' hbody' => cases some_det har har'; cases ihb hbody'
    | loopEsc har' hbody' hfl' =>
      cases some_det har har'
      cases ihb hbody'
      exact (esc_brk hfl').elim
  | loopBrk har hbody ihb =>
    intro r₂ h₂
    cases h₂ with
    | loopOk har' hbody' => cases some_det har har'; cases ihb hbody'
    | loopBack har' hbody' => cases some_det har har'; cases ihb hbody'
    | loopBrk har' hbody' => cases some_det har har'; cases ihb hbody'; rfl
    | loopEsc har' hbody' hfl' =>
      cases some_det har har'
      cases ihb hbody'
      exact (esc_brk hfl').elim
  | loopEsc har hbody hfl ihb =>
    intro r₂ h₂
    cases h₂ with
    | loopOk har' hbody' =>
      cases some_det har har'
      cases ihb hbody'
      exact (esc_normal hfl).elim
    | loopBack har' hbody' =>
      cases some_det har har'
      cases ihb hbody'
      exact (esc_brk hfl).elim
    | loopBrk har' hbody' =>
      cases some_det har har'
      cases ihb hbody'
      exact (esc_brk hfl).elim
    | loopEsc har' hbody' =>
      cases some_det har har'
      exact ihb hbody'
  | ifOk hc hb har harm hvs hk ihc iharm ihk =>
    intro r₂ h₂
    cases h₂ with
    | ifOk hc' hb' har' harm' hvs' hk' =>
      cases ihc hc'
      cases some_det hb hb'
      cases some_det har har'
      cases iharm harm'
      cases some_det hvs hvs'
      exact ihk hk'
    | ifBrk hc' hb' har' harm' =>
      cases ihc hc'
      cases some_det hb hb'
      cases some_det har har'
      cases iharm harm'
      exact (blockVals_brk hvs).elim
    | ifEsc hc' hb' har' harm' hfl' =>
      cases ihc hc'
      cases some_det hb hb'
      cases some_det har har'
      cases iharm harm'
      exact (blockVals_esc hvs hfl').elim
    | ifAbort hc' hfl' => exact (nn hfl' (ihc hc').symm).elim
  | ifBrk hc hb har harm ihc iharm =>
    intro r₂ h₂
    cases h₂ with
    | ifOk hc' hb' har' harm' hvs' =>
      cases ihc hc'
      cases some_det hb hb'
      cases some_det har har'
      cases iharm harm'
      exact (blockVals_brk hvs').elim
    | ifBrk hc' hb' har' harm' =>
      cases ihc hc'
      cases some_det hb hb'
      cases some_det har har'
      cases iharm harm'
      rfl
    | ifEsc hc' hb' har' harm' hfl' =>
      cases ihc hc'
      cases some_det hb hb'
      cases some_det har har'
      cases iharm harm'
      exact (esc_brk hfl').elim
    | ifAbort hc' hfl' => exact (nn hfl' (ihc hc').symm).elim
  | ifEsc hc hb har harm hfl ihc iharm =>
    intro r₂ h₂
    cases h₂ with
    | ifOk hc' hb' har' harm' hvs' =>
      cases ihc hc'
      cases some_det hb hb'
      cases some_det har har'
      cases iharm harm'
      exact (blockVals_esc hvs' hfl).elim
    | ifBrk hc' hb' har' harm' =>
      cases ihc hc'
      cases some_det hb hb'
      cases some_det har har'
      cases iharm harm'
      exact (esc_brk hfl).elim
    | ifEsc hc' hb' har' harm' =>
      cases ihc hc'
      cases some_det hb hb'
      cases some_det har har'
      exact iharm harm'
    | ifAbort hc' hfl' => exact (nn hfl' (ihc hc').symm).elim
  | ifAbort hc hfl ihc =>
    intro r₂ h₂
    cases h₂ with
    | ifOk hc' => exact (nn hfl (ihc hc')).elim
    | ifBrk hc' => exact (nn hfl (ihc hc')).elim
    | ifEsc hc' => exact (nn hfl (ihc hc')).elim
    | ifAbort hc' => exact ihc hc'
  | callIndOk hargs hres hfi hty hcall hvs hk iha ihk =>
    intro r₂ h₂
    cases h₂ with
    | argsAbort hargs' hfl' => exact (nn hfl' (iha hargs').symm).elim
    | opOk _ _ hflat' => exact (flat_x hflat' rfl).elim
    | opStop _ _ hflat' => exact (flat_x hflat' rfl).elim
    | callIndOk hargs' hres' hfi' hty' hcall' hvs' hk' =>
      obtain ⟨rfl, rfl, rfl, hi, rfl⟩ := nrmI (iha hargs')
      subst hi
      cases Silmaril.Wasm.Abstract.CallRes.indRes_unique hres hres'
      cases some_det hfi hfi'
      cases some_det hty hty'
      cases hC _ _ _ _ _ hcall hcall'
      cases some_det hvs hvs'
      exact ihk hk'
    | callIndRes hargs' hres' =>
      obtain ⟨rfl, rfl, rfl, hi, rfl⟩ := nrmI (iha hargs')
      subst hi
      cases Silmaril.Wasm.Abstract.CallRes.indRes_unique hres hres'
    | callIndStop hargs' hres' hfi' hty' hcall' hfl' =>
      obtain ⟨rfl, rfl, rfl, hi, rfl⟩ := nrmI (iha hargs')
      subst hi
      cases Silmaril.Wasm.Abstract.CallRes.indRes_unique hres hres'
      cases some_det hfi hfi'
      cases some_det hty hty'
      cases hC _ _ _ _ _ hcall hcall'
      exact (not_abrupt_of_retVals hvs hfl').elim
    | tail _ hres' => cases hres'
    | tailRes _ hres' => cases hres'
  | callIndRes hargs hres iha =>
    intro r₂ h₂
    cases h₂ with
    | argsAbort hargs' hfl' => exact (nn hfl' (iha hargs').symm).elim
    | opOk _ _ hflat' => exact (flat_x hflat' rfl).elim
    | opStop _ _ hflat' => exact (flat_x hflat' rfl).elim
    | callIndOk hargs' hres' =>
      obtain ⟨rfl, rfl, rfl, hi, rfl⟩ := nrmI (iha hargs')
      subst hi
      cases Silmaril.Wasm.Abstract.CallRes.indRes_unique hres hres'
    | callIndRes hargs' hres' =>
      obtain ⟨rfl, rfl, rfl, hi, rfl⟩ := nrmI (iha hargs')
      rfl
    | callIndStop hargs' hres' =>
      obtain ⟨rfl, rfl, rfl, hi, rfl⟩ := nrmI (iha hargs')
      subst hi
      cases Silmaril.Wasm.Abstract.CallRes.indRes_unique hres hres'
    | tail _ hres' => cases hres'
    | tailRes _ hres' => cases hres'
  | callIndStop hargs hres hfi hty hcall hfl iha =>
    intro r₂ h₂
    cases h₂ with
    | argsAbort hargs' hfl' => exact (nn hfl' (iha hargs').symm).elim
    | opOk _ _ hflat' => exact (flat_x hflat' rfl).elim
    | opStop _ _ hflat' => exact (flat_x hflat' rfl).elim
    | callIndOk hargs' hres' hfi' hty' hcall' hvs' =>
      obtain ⟨rfl, rfl, rfl, hi, rfl⟩ := nrmI (iha hargs')
      subst hi
      cases Silmaril.Wasm.Abstract.CallRes.indRes_unique hres hres'
      cases some_det hfi hfi'
      cases some_det hty hty'
      cases hC _ _ _ _ _ hcall hcall'
      exact (not_abrupt_of_retVals hvs' hfl).elim
    | callIndRes hargs' hres' =>
      obtain ⟨rfl, rfl, rfl, hi, rfl⟩ := nrmI (iha hargs')
      subst hi
      cases Silmaril.Wasm.Abstract.CallRes.indRes_unique hres hres'
    | callIndStop hargs' hres' hfi' hty' hcall' =>
      obtain ⟨rfl, rfl, rfl, hi, rfl⟩ := nrmI (iha hargs')
      subst hi
      cases Silmaril.Wasm.Abstract.CallRes.indRes_unique hres hres'
      cases some_det hfi hfi'
      cases some_det hty hty'
      cases hC _ _ _ _ _ hcall hcall'
      rfl
    | tail _ hres' => cases hres'
    | tailRes _ hres' => cases hres'
  | callRefOk hargs hfi hty hcall hvs hk iha ihk =>
    intro r₂ h₂
    cases h₂ with
    | argsAbort hargs' hfl' => exact (nn hfl' (iha hargs').symm).elim
    | opOk _ _ hflat' => exact (flat_x hflat' rfl).elim
    | opStop _ _ hflat' => exact (flat_x hflat' rfl).elim
    | callRefOk hargs' hfi' hty' hcall' hvs' hk' =>
      obtain ⟨rfl, rfl, h⟩ := nrm (iha hargs')
      cases h
      cases some_det hfi hfi'
      cases some_det hty hty'
      cases hC _ _ _ _ _ hcall hcall'
      cases some_det hvs hvs'
      exact ihk hk'
    | callRefNull hargs' => obtain ⟨rfl, rfl, h⟩ := nrm (iha hargs'); cases h
    | callRefStop hargs' hfi' hty' hcall' hfl' =>
      obtain ⟨rfl, rfl, h⟩ := nrm (iha hargs')
      cases h
      cases some_det hfi hfi'
      cases some_det hty hty'
      cases hC _ _ _ _ _ hcall hcall'
      exact (not_abrupt_of_retVals hvs hfl').elim
    | tail _ hres' => cases hres'
    | tailRes _ hres' => cases hres'
  | callRefNull hargs iha =>
    intro r₂ h₂
    cases h₂ with
    | argsAbort hargs' hfl' => exact (nn hfl' (iha hargs').symm).elim
    | opOk _ _ hflat' => exact (flat_x hflat' rfl).elim
    | opStop _ _ hflat' => exact (flat_x hflat' rfl).elim
    | callRefOk hargs' => obtain ⟨rfl, rfl, h⟩ := nrm (iha hargs'); cases h
    | callRefNull hargs' => obtain ⟨rfl, rfl, h⟩ := nrm (iha hargs'); cases h; rfl
    | callRefStop hargs' => obtain ⟨rfl, rfl, h⟩ := nrm (iha hargs'); cases h
    | tail _ hres' => cases hres'
    | tailRes _ hres' => cases hres'
  | callRefStop hargs hfi hty hcall hfl iha =>
    intro r₂ h₂
    cases h₂ with
    | argsAbort hargs' hfl' => exact (nn hfl' (iha hargs').symm).elim
    | opOk _ _ hflat' => exact (flat_x hflat' rfl).elim
    | opStop _ _ hflat' => exact (flat_x hflat' rfl).elim
    | callRefOk hargs' hfi' hty' hcall' hvs' =>
      obtain ⟨rfl, rfl, h⟩ := nrm (iha hargs')
      cases h
      cases some_det hfi hfi'
      cases some_det hty hty'
      cases hC _ _ _ _ _ hcall hcall'
      exact (not_abrupt_of_retVals hvs' hfl).elim
    | callRefNull hargs' => obtain ⟨rfl, rfl, h⟩ := nrm (iha hargs'); cases h
    | callRefStop hargs' hfi' hty' hcall' =>
      obtain ⟨rfl, rfl, h⟩ := nrm (iha hargs')
      cases h
      cases some_det hfi hfi'
      cases some_det hty hty'
      cases hC _ _ _ _ _ hcall hcall'
      rfl
    | tail _ hres' => cases hres'
    | tailRes _ hres' => cases hres'
  | tail hargs hres hfi hty hcall hfl iha =>
    intro r₂ h₂
    cases h₂ with
    | argsAbort hargs' hfl' => exact (nn hfl' (iha hargs').symm).elim
    | callOk => cases hres
    | callTrap => cases hres
    | callThrow => cases hres
    | opOk _ _ hflat' => exact (flat_x hflat' (isXCall_of_tailRes hres)).elim
    | opStop _ _ hflat' => exact (flat_x hflat' (isXCall_of_tailRes hres)).elim
    | callIndOk => cases hres
    | callIndRes => cases hres
    | callIndStop => cases hres
    | callRefOk => cases hres
    | callRefNull => cases hres
    | callRefStop => cases hres
    | tail hargs' hres' hfi' hty' hcall' =>
      obtain ⟨rfl, rfl, rfl⟩ := nrm (iha hargs')
      cases tailRes_unique hres hres'
      cases some_det hfi hfi'
      cases some_det hty hty'
      cases hC _ _ _ _ _ hcall hcall'
      rfl
    | tailRes hargs' hres' =>
      obtain ⟨rfl, rfl, rfl⟩ := nrm (iha hargs')
      cases tailRes_unique hres hres'
  | tailRes hargs hres iha =>
    intro r₂ h₂
    cases h₂ with
    | argsAbort hargs' hfl' => exact (nn hfl' (iha hargs').symm).elim
    | callOk => cases hres
    | callTrap => cases hres
    | callThrow => cases hres
    | opOk _ _ hflat' => exact (flat_x hflat' (isXCall_of_tailRes hres)).elim
    | opStop _ _ hflat' => exact (flat_x hflat' (isXCall_of_tailRes hres)).elim
    | callIndOk => cases hres
    | callIndRes => cases hres
    | callIndStop => cases hres
    | callRefOk => cases hres
    | callRefNull => cases hres
    | callRefStop => cases hres
    | tail hargs' hres' =>
      obtain ⟨rfl, rfl, rfl⟩ := nrm (iha hargs')
      cases tailRes_unique hres hres'
    | tailRes hargs' =>
      obtain ⟨rfl, rfl, rfl⟩ := nrm (iha hargs')
      rfl

/-! ## The closure is functional -/

theorem code_det {fi : FuncInst H} {fn fn' : Func} (h : fi.code = .wasm fn) (h' : fi.code = .wasm fn') :
    fn = fn' := by rw [h] at h'; cases h'; rfl

/-- **The closed extended call relation is functional.** -/
theorem closedCallX_agree : Agree (closedCallX : CallRel H) closedCallX := by
  let P : CallRel H := fun s a args o =>
    closedCallX s a args o ∧ ∀ o', closedCallX s a args o' → o = o'
  have hP : (closedCallX : CallRel H) ≤ P := by
    refine OrderHom.lfp_le _ ?_
    rintro s a args o ⟨fi, fn, ps, rs, f₂, hfi, hc, hty, d⟩
    refine ⟨?_, fun o' h' => ?_⟩
    · rw [closedCallX_fixpoint]
      exact ⟨fi, fn, ps, rs, f₂, hfi, hc, hty, d.mono fun _ _ _ _ h => h.1⟩
    · rw [closedCallX_fixpoint] at h'
      obtain ⟨fi', fn', ps', rs', f₂', hfi', hc', hty', d'⟩ := h'
      cases some_det hfi hfi'
      cases code_det hc hc'
      have := evalOX_det (fun _ _ _ _ _ h₁ h₂ => h₁.2 _ h₂) d d'
      obtain ⟨o₁, o₂⟩ := o
      obtain ⟨o₁', o₂'⟩ := o'
      cases this
      rfl
  exact fun s a args o₁ o₂ h₁ h₂ => (hP s a args o₁ h₁).2 o₂ h₂

/-- The callee of a closed call: its body's run ends as the call's answer. -/
theorem callee_det {s₁ s₂ s₂' : Store H} {a : Nat} {args : List Val} {fi : FuncInst H}
    {fn : Func} {f₂ : Frame} {fl fl' : Flow} (hcall : closedCallX s₁ a args (s₂, fl))
    (hfi : s₁.funcs[a]? = some fi) (hc : fi.code = .wasm fn)
    (hbody : EvalOX closedCallX s₁ (Frame.forCall fi.module args fn.locals) [] (liftInstrs fn.body)
      (s₂', f₂, fl')) : s₂ = s₂' ∧ fl = fl' := by
  rw [closedCallX_fixpoint] at hcall
  obtain ⟨fi', fn', ps', rs', f₂', hfi', hc', hty', d⟩ := hcall
  cases some_det hfi hfi'
  cases code_det hc hc'
  cases evalOX_det closedCallX_agree d hbody
  exact ⟨rfl, rfl⟩

end Silmaril.Proofs.Wasm.Abstract.XDiverge
