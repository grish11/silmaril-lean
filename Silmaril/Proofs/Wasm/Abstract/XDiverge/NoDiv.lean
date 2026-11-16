module

public import Silmaril.Proofs.Wasm.Abstract.XDiverge.Det

/-!
Proofs for `Silmaril.Wasm.Abstract.XDiverge.Thms`: **answers exclude
divergence**. A problem with an outcome in the closed extended semantics does
not diverge (`not_evalDivX_of_evalOX`).

Callees are not subderivations, so the proof is a least-fixpoint induction:
every closed call's callee body does not diverge (`closedCallX_le_noDiv`). Its
step is an induction on the body's run under the oracle `P` (closed calls whose
callees do not diverge, `noDiv_of_evalOX`), unfolding the divergence once at
each level and matching each terminating part by determinism (`evalOX_det`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.XDiverge

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel funcs_of_func?)
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.XRecursion Silmaril.Wasm.Abstract.XDiverge
open Silmaril.Proofs.Wasm.Abstract.CallX (tailRes_unique)

variable {H : Type}

/-- The callee of a call does not diverge. -/
def CalleeNoDiv : CallRel H := fun s a args _ =>
  ∀ (fi : FuncInst H) (fn : Func), s.funcs[a]? = some fi → fi.code = .wasm fn →
    ¬ EvalDivX s (Frame.forCall fi.module args fn.locals) [] (liftInstrs fn.body)

section
variable {C : CallRel H} (hCl : C ≤ closedCallX) (hN : C ≤ CalleeNoDiv)
include hCl hN

omit hN in
theorem agree_C : Agree C closedCallX :=
  fun s a args o₁ o₂ h₁ h₂ => closedCallX_agree s a args o₁ o₂ (hCl _ _ _ _ h₁) h₂

omit hN in
theorem det_C {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r₁ r₂ : Store H × Frame × Flow} (h₁ : EvalOX C s f stk es r₁)
    (h₂ : EvalOX closedCallX s f stk es r₂) : r₁ = r₂ :=
  evalOX_det (agree_C hCl) h₁ h₂

/-- A run under `C` does not diverge. -/
theorem noDiv_of_evalOX {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (h : EvalOX C s f stk es r) : ¬ EvalDivX s f stk es := by
  induction h with
  | nil => intro hd; cases evalDivX_unfold.1 hd
  | argsAbort hargs hfl ih =>
    intro hd
    cases evalDivX_unfold.1 hd with
    | args h => exact ih h
    | callee hargs' => exact nn hfl (det_C hCl hargs hargs')
    | callRet hargs' => exact nn hfl (det_C hCl hargs hargs')
    | opK _ hargs' => exact nn hfl (det_C hCl hargs hargs')
    | callIndCallee hargs' => exact nn hfl (det_C hCl hargs hargs')
    | callIndRet hargs' => exact nn hfl (det_C hCl hargs hargs')
    | callRefCallee hargs' => exact nn hfl (det_C hCl hargs hargs')
    | callRefRet hargs' => exact nn hfl (det_C hCl hargs hargs')
    | tailCallee hargs' => exact nn hfl (det_C hCl hargs hargs')
  | callOk hargs hfi hty hcall hvs hk iha ihk =>
    intro hd
    cases evalDivX_unfold.1 hd with
    | args h => exact iha h
    | callee hargs' hfi' hcode' hty' h =>
      obtain ⟨rfl, rfl, rfl⟩ := nrm (det_C hCl hargs hargs')
      obtain ⟨rfl, rfl⟩ := func?_det hfi hfi'
      cases some_det hty hty'
      exact hN _ _ _ _ hcall _ _ (funcs_of_func? hfi) hcode' h
    | callRet hargs' hfi' hcode' hty' hbody' hvs' h =>
      obtain ⟨rfl, rfl, rfl⟩ := nrm (det_C hCl hargs hargs')
      obtain ⟨rfl, rfl⟩ := func?_det hfi hfi'
      cases some_det hty hty'
      obtain ⟨rfl, rfl⟩ := callee_det (hCl _ _ _ _ hcall) (funcs_of_func? hfi) hcode' hbody'
      cases some_det hvs hvs'
      exact ihk h
    | opK hi => exact hi _ rfl
    | tailCallee _ hres => cases hres
  | callTrap hargs hfi hty hcall iha =>
    intro hd
    cases evalDivX_unfold.1 hd with
    | args h => exact iha h
    | callee hargs' hfi' hcode' hty' h =>
      obtain ⟨rfl, rfl, rfl⟩ := nrm (det_C hCl hargs hargs')
      obtain ⟨rfl, rfl⟩ := func?_det hfi hfi'
      cases some_det hty hty'
      exact hN _ _ _ _ hcall _ _ (funcs_of_func? hfi) hcode' h
    | callRet hargs' hfi' hcode' hty' hbody' hvs' =>
      obtain ⟨rfl, rfl, rfl⟩ := nrm (det_C hCl hargs hargs')
      obtain ⟨rfl, rfl⟩ := func?_det hfi hfi'
      cases some_det hty hty'
      obtain ⟨rfl, rfl⟩ := callee_det (hCl _ _ _ _ hcall) (funcs_of_func? hfi) hcode' hbody'
      exact retVals_trap hvs'
    | opK hi => exact hi _ rfl
    | tailCallee _ hres => cases hres
  | callThrow hargs hfi hty hcall iha =>
    intro hd
    cases evalDivX_unfold.1 hd with
    | args h => exact iha h
    | callee hargs' hfi' hcode' hty' h =>
      obtain ⟨rfl, rfl, rfl⟩ := nrm (det_C hCl hargs hargs')
      obtain ⟨rfl, rfl⟩ := func?_det hfi hfi'
      cases some_det hty hty'
      exact hN _ _ _ _ hcall _ _ (funcs_of_func? hfi) hcode' h
    | callRet hargs' hfi' hcode' hty' hbody' hvs' =>
      obtain ⟨rfl, rfl, rfl⟩ := nrm (det_C hCl hargs hargs')
      obtain ⟨rfl, rfl⟩ := func?_det hfi hfi'
      cases some_det hty hty'
      obtain ⟨rfl, rfl⟩ := callee_det (hCl _ _ _ _ hcall) (funcs_of_func? hfi) hcode' hbody'
      exact retVals_throw hvs'
    | opK hi => exact hi _ rfl
    | tailCallee _ hres => cases hres
  | opOk hi hargs hflat hk iha ihk =>
    intro hd
    cases evalDivX_unfold.1 hd with
    | args h => exact iha h
    | callee => exact hi _ rfl
    | callRet => exact hi _ rfl
    | opK _ hargs' hflat' h =>
      obtain ⟨rfl, rfl, rfl⟩ := nrm (det_C hCl hargs hargs')
      cases some_det hflat hflat'
      exact ihk h
    | callIndCallee => exact flat_x hflat rfl
    | callIndRet => exact flat_x hflat rfl
    | callRefCallee => exact flat_x hflat rfl
    | callRefRet => exact flat_x hflat rfl
    | tailCallee _ hres => exact flat_x hflat (isXCall_of_tailRes hres)
  | opStop hi hargs hflat hfl iha =>
    intro hd
    cases evalDivX_unfold.1 hd with
    | args h => exact iha h
    | callee => exact hi _ rfl
    | callRet => exact hi _ rfl
    | opK _ hargs' hflat' =>
      obtain ⟨rfl, rfl, rfl⟩ := nrm (det_C hCl hargs hargs')
      cases some_det hflat hflat'
      exact hfl trivial
    | callIndCallee => exact flat_x hflat rfl
    | callIndRet => exact flat_x hflat rfl
    | callRefCallee => exact flat_x hflat rfl
    | callRefRet => exact flat_x hflat rfl
    | tailCallee _ hres => exact flat_x hflat (isXCall_of_tailRes hres)
  | blockOk har hbody hvs hk ihb ihk =>
    intro hd
    cases evalDivX_unfold.1 hd with
    | block har' h => cases some_det har har'; exact ihb h
    | blockK har' hbody' hvs' h =>
      cases some_det har har'
      cases det_C hCl hbody hbody'
      cases some_det hvs hvs'
      exact ihk h
  | blockBrk har hbody ihb =>
    intro hd
    cases evalDivX_unfold.1 hd with
    | block har' h => cases some_det har har'; exact ihb h
    | blockK har' hbody' hvs' =>
      cases some_det har har'
      cases det_C hCl hbody hbody'
      exact blockVals_brk hvs'
  | blockEsc har hbody hfl ihb =>
    intro hd
    cases evalDivX_unfold.1 hd with
    | block har' h => cases some_det har har'; exact ihb h
    | blockK har' hbody' hvs' =>
      cases some_det har har'
      cases det_C hCl hbody hbody'
      exact blockVals_esc hvs' hfl
  | loopOk har hbody hk ihb ihk =>
    intro hd
    cases evalDivX_unfold.1 hd with
    | loop har' h => cases some_det har har'; exact ihb h
    | loopK har' hbody' h =>
      cases some_det har har'
      cases det_C hCl hbody hbody'
      exact ihk h
    | loopBack har' hbody' =>
      cases some_det har har'
      cases det_C hCl hbody hbody'
  | loopBack har hbody hk ihb ihk =>
    intro hd
    cases evalDivX_unfold.1 hd with
    | loop har' h => cases some_det har har'; exact ihb h
    | loopK har' hbody' =>
      cases some_det har har'
      cases det_C hCl hbody hbody'
    | loopBack har' hbody' h =>
      cases some_det har har'
      cases det_C hCl hbody hbody'
      exact ihk h
  | loopBrk har hbody ihb =>
    intro hd
    cases evalDivX_unfold.1 hd with
    | loop har' h => cases some_det har har'; exact ihb h
    | loopK har' hbody' =>
      cases some_det har har'
      cases det_C hCl hbody hbody'
    | loopBack har' hbody' =>
      cases some_det har har'
      cases det_C hCl hbody hbody'
  | loopEsc har hbody hfl ihb =>
    intro hd
    cases evalDivX_unfold.1 hd with
    | loop har' h => cases some_det har har'; exact ihb h
    | loopK har' hbody' =>
      cases some_det har har'
      cases det_C hCl hbody hbody'
      exact esc_normal hfl
    | loopBack har' hbody' =>
      cases some_det har har'
      cases det_C hCl hbody hbody'
      exact esc_brk hfl
  | ifOk hc hb har harm hvs hk ihc iharm ihk =>
    intro hd
    cases evalDivX_unfold.1 hd with
    | cond h => exact ihc h
    | arm hc' hb' har' h =>
      cases det_C hCl hc hc'
      cases some_det hb hb'
      cases some_det har har'
      exact iharm h
    | ifK hc' hb' har' harm' hvs' h =>
      cases det_C hCl hc hc'
      cases some_det hb hb'
      cases some_det har har'
      cases det_C hCl harm harm'
      cases some_det hvs hvs'
      exact ihk h
  | ifBrk hc hb har harm ihc iharm =>
    intro hd
    cases evalDivX_unfold.1 hd with
    | cond h => exact ihc h
    | arm hc' hb' har' h =>
      cases det_C hCl hc hc'
      cases some_det hb hb'
      cases some_det har har'
      exact iharm h
    | ifK hc' hb' har' harm' hvs' =>
      cases det_C hCl hc hc'
      cases some_det hb hb'
      cases some_det har har'
      cases det_C hCl harm harm'
      exact blockVals_brk hvs'
  | ifEsc hc hb har harm hfl ihc iharm =>
    intro hd
    cases evalDivX_unfold.1 hd with
    | cond h => exact ihc h
    | arm hc' hb' har' h =>
      cases det_C hCl hc hc'
      cases some_det hb hb'
      cases some_det har har'
      exact iharm h
    | ifK hc' hb' har' harm' hvs' =>
      cases det_C hCl hc hc'
      cases some_det hb hb'
      cases some_det har har'
      cases det_C hCl harm harm'
      exact blockVals_esc hvs' hfl
  | ifAbort hc hfl ihc =>
    intro hd
    cases evalDivX_unfold.1 hd with
    | cond h => exact ihc h
    | arm hc' => exact nn hfl (det_C hCl hc hc')
    | ifK hc' => exact nn hfl (det_C hCl hc hc')
  | callIndOk hargs hres hfi hty hcall hvs hk iha ihk =>
    intro hd
    cases evalDivX_unfold.1 hd with
    | args h => exact iha h
    | opK _ _ hflat' => exact flat_x hflat' rfl
    | callIndCallee hargs' hres' hfi' hcode' hty' h =>
      obtain ⟨rfl, rfl, rfl, hi, rfl⟩ := nrmI (det_C hCl hargs hargs')
      subst hi
      cases Silmaril.Wasm.Abstract.CallRes.indRes_unique hres hres'
      cases some_det hfi hfi'
      cases some_det hty hty'
      exact hN _ _ _ _ hcall _ _ hfi hcode' h
    | callIndRet hargs' hres' hfi' hcode' hty' hbody' hvs' h =>
      obtain ⟨rfl, rfl, rfl, hi, rfl⟩ := nrmI (det_C hCl hargs hargs')
      subst hi
      cases Silmaril.Wasm.Abstract.CallRes.indRes_unique hres hres'
      cases some_det hfi hfi'
      cases some_det hty hty'
      obtain ⟨rfl, rfl⟩ := callee_det (hCl _ _ _ _ hcall) hfi hcode' hbody'
      cases some_det hvs hvs'
      exact ihk h
    | tailCallee _ hres' => cases hres'
  | callIndRes hargs hres iha =>
    intro hd
    cases evalDivX_unfold.1 hd with
    | args h => exact iha h
    | opK _ _ hflat' => exact flat_x hflat' rfl
    | callIndCallee hargs' hres' =>
      obtain ⟨rfl, rfl, rfl, hi, rfl⟩ := nrmI (det_C hCl hargs hargs')
      subst hi
      cases Silmaril.Wasm.Abstract.CallRes.indRes_unique hres hres'
    | callIndRet hargs' hres' =>
      obtain ⟨rfl, rfl, rfl, hi, rfl⟩ := nrmI (det_C hCl hargs hargs')
      subst hi
      cases Silmaril.Wasm.Abstract.CallRes.indRes_unique hres hres'
    | tailCallee _ hres' => cases hres'
  | callIndStop hargs hres hfi hty hcall hfl iha =>
    intro hd
    cases evalDivX_unfold.1 hd with
    | args h => exact iha h
    | opK _ _ hflat' => exact flat_x hflat' rfl
    | callIndCallee hargs' hres' hfi' hcode' hty' h =>
      obtain ⟨rfl, rfl, rfl, hi, rfl⟩ := nrmI (det_C hCl hargs hargs')
      subst hi
      cases Silmaril.Wasm.Abstract.CallRes.indRes_unique hres hres'
      cases some_det hfi hfi'
      cases some_det hty hty'
      exact hN _ _ _ _ hcall _ _ hfi hcode' h
    | callIndRet hargs' hres' hfi' hcode' hty' hbody' hvs' =>
      obtain ⟨rfl, rfl, rfl, hi, rfl⟩ := nrmI (det_C hCl hargs hargs')
      subst hi
      cases Silmaril.Wasm.Abstract.CallRes.indRes_unique hres hres'
      cases some_det hfi hfi'
      cases some_det hty hty'
      obtain ⟨rfl, rfl⟩ := callee_det (hCl _ _ _ _ hcall) hfi hcode' hbody'
      exact not_abrupt_of_retVals hvs' hfl
    | tailCallee _ hres' => cases hres'
  | callRefOk hargs hfi hty hcall hvs hk iha ihk =>
    intro hd
    cases evalDivX_unfold.1 hd with
    | args h => exact iha h
    | opK _ _ hflat' => exact flat_x hflat' rfl
    | callRefCallee hargs' hfi' hcode' hty' h =>
      obtain ⟨rfl, rfl, he⟩ := nrm (det_C hCl hargs hargs')
      cases he
      cases some_det hfi hfi'
      cases some_det hty hty'
      exact hN _ _ _ _ hcall _ _ hfi hcode' h
    | callRefRet hargs' hfi' hcode' hty' hbody' hvs' h =>
      obtain ⟨rfl, rfl, he⟩ := nrm (det_C hCl hargs hargs')
      cases he
      cases some_det hfi hfi'
      cases some_det hty hty'
      obtain ⟨rfl, rfl⟩ := callee_det (hCl _ _ _ _ hcall) hfi hcode' hbody'
      cases some_det hvs hvs'
      exact ihk h
    | tailCallee _ hres' => cases hres'
  | callRefNull hargs iha =>
    intro hd
    cases evalDivX_unfold.1 hd with
    | args h => exact iha h
    | opK _ _ hflat' => exact flat_x hflat' rfl
    | callRefCallee hargs' => obtain ⟨-, -, he⟩ := nrm (det_C hCl hargs hargs'); cases he
    | callRefRet hargs' => obtain ⟨-, -, he⟩ := nrm (det_C hCl hargs hargs'); cases he
    | tailCallee _ hres' => cases hres'
  | callRefStop hargs hfi hty hcall hfl iha =>
    intro hd
    cases evalDivX_unfold.1 hd with
    | args h => exact iha h
    | opK _ _ hflat' => exact flat_x hflat' rfl
    | callRefCallee hargs' hfi' hcode' hty' h =>
      obtain ⟨rfl, rfl, he⟩ := nrm (det_C hCl hargs hargs')
      cases he
      cases some_det hfi hfi'
      cases some_det hty hty'
      exact hN _ _ _ _ hcall _ _ hfi hcode' h
    | callRefRet hargs' hfi' hcode' hty' hbody' hvs' =>
      obtain ⟨rfl, rfl, he⟩ := nrm (det_C hCl hargs hargs')
      cases he
      cases some_det hfi hfi'
      cases some_det hty hty'
      obtain ⟨rfl, rfl⟩ := callee_det (hCl _ _ _ _ hcall) hfi hcode' hbody'
      exact not_abrupt_of_retVals hvs' hfl
    | tailCallee _ hres' => cases hres'
  | tail hargs hres hfi hty hcall hfl iha =>
    intro hd
    cases evalDivX_unfold.1 hd with
    | args h => exact iha h
    | callee => cases hres
    | callRet => cases hres
    | opK _ _ hflat' => exact flat_x hflat' (isXCall_of_tailRes hres)
    | callIndCallee => cases hres
    | callIndRet => cases hres
    | callRefCallee => cases hres
    | callRefRet => cases hres
    | tailCallee hargs' hres' hfi' hcode' hty' h =>
      obtain ⟨rfl, rfl, rfl⟩ := nrm (det_C hCl hargs hargs')
      cases tailRes_unique hres hres'
      cases some_det hfi hfi'
      cases some_det hty hty'
      exact hN _ _ _ _ hcall _ _ hfi hcode' h
  | tailRes hargs hres iha =>
    intro hd
    cases evalDivX_unfold.1 hd with
    | args h => exact iha h
    | callee => cases hres
    | callRet => cases hres
    | opK _ _ hflat' => exact flat_x hflat' (isXCall_of_tailRes hres)
    | callIndCallee => cases hres
    | callIndRet => cases hres
    | callRefCallee => cases hres
    | callRefRet => cases hres
    | tailCallee hargs' hres' =>
      obtain ⟨rfl, rfl, rfl⟩ := nrm (det_C hCl hargs hargs')
      cases tailRes_unique hres hres'

end

/-- **Closed calls' callees do not diverge.** -/
theorem closedCallX_le_noDiv : (closedCallX : CallRel H) ≤ CalleeNoDiv := by
  let P : CallRel H := fun s a args o => closedCallX s a args o ∧ CalleeNoDiv s a args o
  have hP : (closedCallX : CallRel H) ≤ P := by
    refine OrderHom.lfp_le _ ?_
    rintro s a args o ⟨fi, fn, ps, rs, f₂, hfi, hc, hty, d⟩
    refine ⟨?_, fun fi' fn' hfi' hc' => ?_⟩
    · rw [closedCallX_fixpoint]
      exact ⟨fi, fn, ps, rs, f₂, hfi, hc, hty, d.mono fun _ _ _ _ h => h.1⟩
    · cases some_det hfi hfi'
      cases code_det hc hc'
      exact noDiv_of_evalOX (fun _ _ _ _ h => h.1) (fun _ _ _ _ h => h.2) d
  exact fun s a args o h => (hP s a args o h).2

/-- **Answers exclude divergence.** -/
theorem not_evalDivX_of_evalOX {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (h : EvalOX closedCallX s f stk es r) : ¬ EvalDivX s f stk es :=
  noDiv_of_evalOX le_rfl closedCallX_le_noDiv h

end Silmaril.Proofs.Wasm.Abstract.XDiverge
