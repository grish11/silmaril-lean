module

public import Silmaril.Wasm.Abstract.CallXE.Defs

/-!
Proofs for `Silmaril.Wasm.Abstract.CallXE.Thms`: `EvalOXE` is a conservative extension of
`CallX.EvalOX` (`of_evalOX`, every run; `to_evalOX`, on exception-free code).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.CallXE

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel)
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXE

variable {H : Type}

/-- Every `EvalOX` run is an `EvalOXE` run. -/
theorem of_evalOX {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (h : EvalOX C s f stk es r) : EvalOXE C s f stk es r := by
  induction h with
  | nil => exact .nil
  | argsAbort _ hfl ih => exact .argsAbort ih hfl
  | callOk _ hfi hty hcall hvs _ ih₁ ih₂ => exact .callOk ih₁ hfi hty hcall hvs ih₂
  | callTrap _ hfi hty hcall ih => exact .callTrap ih hfi hty hcall
  | callThrow _ hfi hty hcall ih => exact .callThrow ih hfi hty hcall
  | opOk hi _ hflat _ ih₁ ih₂ => exact .opOk hi ih₁ hflat ih₂
  | opStop hi _ hflat hfl ih => exact .opStop hi ih hflat hfl
  | blockOk har _ hvs _ ih₁ ih₂ => exact .blockOk har ih₁ hvs ih₂
  | blockBrk har _ ih => exact .blockBrk har ih
  | blockEsc har _ hfl ih => exact .blockEsc har ih hfl
  | loopOk har _ _ ih₁ ih₂ => exact .loopOk har ih₁ ih₂
  | loopBack har _ _ ih₁ ih₂ => exact .loopBack har ih₁ ih₂
  | loopBrk har _ ih => exact .loopBrk har ih
  | loopEsc har _ hfl ih => exact .loopEsc har ih hfl
  | ifOk _ hb har _ hvs _ ih₁ ih₂ ih₃ => exact .ifOk ih₁ hb har ih₂ hvs ih₃
  | ifBrk _ hb har _ ih₁ ih₂ => exact .ifBrk ih₁ hb har ih₂
  | ifEsc _ hb har _ hfl ih₁ ih₂ => exact .ifEsc ih₁ hb har ih₂ hfl
  | ifAbort _ hfl ih => exact .ifAbort ih hfl
  | callIndOk _ hres hfi hty hcall hvs _ ih₁ ih₂ => exact .callIndOk ih₁ hres hfi hty hcall hvs ih₂
  | callIndRes _ hres ih => exact .callIndRes ih hres
  | callIndStop _ hres hfi hty hcall hfl ih => exact .callIndStop ih hres hfi hty hcall hfl
  | callRefOk _ hfi hty hcall hvs _ ih₁ ih₂ => exact .callRefOk ih₁ hfi hty hcall hvs ih₂
  | callRefNull _ ih => exact .callRefNull ih
  | callRefStop _ hfi hty hcall hfl ih => exact .callRefStop ih hfi hty hcall hfl
  | tail _ hres hfi hty hcall hfl ih => exact .tail ih hres hfi hty hcall hfl
  | tailRes _ hres ih => exact .tailRes ih hres

/-- On exception-free code, every `EvalOXE` run is an `EvalOX` run. -/
theorem to_evalOX {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (h : EvalOXE C s f stk es r) :
    ehFreeL es = true → EvalOX C s f stk es r := by
  induction h with
  | nil => intro _; exact .nil
  | argsAbort _ hfl ih =>
    intro hx; simp only [ehFreeL, ehFree, Bool.and_eq_true] at hx
    exact .argsAbort (ih hx.1.2) hfl
  | callOk _ hfi hty hcall hvs _ ih₁ ih₂ =>
    intro hx; simp only [ehFreeL, ehFree, Bool.and_eq_true] at hx
    exact .callOk (ih₁ hx.1.2) hfi hty hcall hvs (ih₂ hx.2)
  | callTrap _ hfi hty hcall ih =>
    intro hx; simp only [ehFreeL, ehFree, Bool.and_eq_true] at hx
    exact .callTrap (ih hx.1.2) hfi hty hcall
  | callThrow _ hfi hty hcall ih =>
    intro hx; simp only [ehFreeL, ehFree, Bool.and_eq_true] at hx
    exact .callThrow (ih hx.1.2) hfi hty hcall
  | opOk hi _ hflat _ ih₁ ih₂ =>
    intro hx; simp only [ehFreeL, ehFree, Bool.and_eq_true] at hx
    exact .opOk hi (ih₁ hx.1.2) hflat (ih₂ hx.2)
  | opStop hi _ hflat hfl ih =>
    intro hx; simp only [ehFreeL, ehFree, Bool.and_eq_true] at hx
    exact .opStop hi (ih hx.1.2) hflat hfl
  | blockOk har _ hvs _ ih₁ ih₂ =>
    intro hx; simp only [ehFreeL, ehFree, Bool.and_eq_true] at hx
    exact .blockOk har (ih₁ hx.1) hvs (ih₂ hx.2)
  | blockBrk har _ ih =>
    intro hx; simp only [ehFreeL, ehFree, Bool.and_eq_true] at hx
    exact .blockBrk har (ih hx.1)
  | blockEsc har _ hfl ih =>
    intro hx; simp only [ehFreeL, ehFree, Bool.and_eq_true] at hx
    exact .blockEsc har (ih hx.1) hfl
  | loopOk har _ _ ih₁ ih₂ =>
    intro hx; simp only [ehFreeL, ehFree, Bool.and_eq_true] at hx
    exact .loopOk har (ih₁ hx.1) (ih₂ hx.2)
  | loopBack har _ _ ih₁ ih₂ =>
    intro hx
    have hx' := hx
    simp only [ehFreeL, ehFree, Bool.and_eq_true] at hx'
    exact .loopBack har (ih₁ hx'.1) (ih₂ hx)
  | loopBrk har _ ih =>
    intro hx; simp only [ehFreeL, ehFree, Bool.and_eq_true] at hx
    exact .loopBrk har (ih hx.1)
  | loopEsc har _ hfl ih =>
    intro hx; simp only [ehFreeL, ehFree, Bool.and_eq_true] at hx
    exact .loopEsc har (ih hx.1) hfl
  | @ifOk s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr fl r _ hb har _ hvs _ ih₁ ih₂ ih₃ =>
    intro hx; simp only [ehFreeL, ehFree, Bool.and_eq_true] at hx
    exact .ifOk (ih₁ hx.1.1.1) hb har (ih₂ (by cases b <;> simp [hx.1.1.2, hx.1.2])) hvs (ih₃ hx.2)
  | @ifBrk s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr k _ hb har _ ih₁ ih₂ =>
    intro hx; simp only [ehFreeL, ehFree, Bool.and_eq_true] at hx
    exact .ifBrk (ih₁ hx.1.1.1) hb har (ih₂ (by cases b <;> simp [hx.1.1.2, hx.1.2]))
  | @ifEsc s s₁ s₂ f f₁ f₂ stk stk₁ cv b bt c t el es np nr fl _ hb har _ hfl ih₁ ih₂ =>
    intro hx; simp only [ehFreeL, ehFree, Bool.and_eq_true] at hx
    exact .ifEsc (ih₁ hx.1.1.1) hb har (ih₂ (by cases b <;> simp [hx.1.1.2, hx.1.2])) hfl
  | ifAbort _ hfl ih =>
    intro hx; simp only [ehFreeL, ehFree, Bool.and_eq_true] at hx
    exact .ifAbort (ih hx.1.1.1) hfl
  | callIndOk _ hres hfi hty hcall hvs _ ih₁ ih₂ =>
    intro hx; simp only [ehFreeL, ehFree, Bool.and_eq_true] at hx
    exact .callIndOk (ih₁ hx.1.2) hres hfi hty hcall hvs (ih₂ hx.2)
  | callIndRes _ hres ih =>
    intro hx; simp only [ehFreeL, ehFree, Bool.and_eq_true] at hx
    exact .callIndRes (ih hx.1.2) hres
  | callIndStop _ hres hfi hty hcall hfl ih =>
    intro hx; simp only [ehFreeL, ehFree, Bool.and_eq_true] at hx
    exact .callIndStop (ih hx.1.2) hres hfi hty hcall hfl
  | callRefOk _ hfi hty hcall hvs _ ih₁ ih₂ =>
    intro hx; simp only [ehFreeL, ehFree, Bool.and_eq_true] at hx
    exact .callRefOk (ih₁ hx.1.2) hfi hty hcall hvs (ih₂ hx.2)
  | callRefNull _ ih =>
    intro hx; simp only [ehFreeL, ehFree, Bool.and_eq_true] at hx
    exact .callRefNull (ih hx.1.2)
  | callRefStop _ hfi hty hcall hfl ih =>
    intro hx; simp only [ehFreeL, ehFree, Bool.and_eq_true] at hx
    exact .callRefStop (ih hx.1.2) hfi hty hcall hfl
  | tail hargs hres hfi hty hcall hfl ih =>
    intro hx; simp only [ehFreeL, ehFree, Bool.and_eq_true] at hx
    exact .tail (ih hx.1.2) hres hfi hty hcall hfl
  | tailRes hargs hres ih =>
    intro hx; simp only [ehFreeL, ehFree, Bool.and_eq_true] at hx
    exact .tailRes (ih hx.1.2) hres

  | throw => intro hx; simp [ehFreeL, ehFree, ehInstr] at hx
  | throwRefNull => intro hx; simp [ehFreeL, ehFree, ehInstr] at hx
  | throwRefExn => intro hx; simp [ehFreeL, ehFree, ehInstr] at hx
  | tryOk => intro hx; simp [ehFreeL, ehFree] at hx
  | tryBrk => intro hx; simp [ehFreeL, ehFree] at hx
  | tryEsc => intro hx; simp [ehFreeL, ehFree] at hx
  | tryCatch => intro hx; simp [ehFreeL, ehFree] at hx
  | tryRethrow => intro hx; simp [ehFreeL, ehFree] at hx

end Silmaril.Proofs.Wasm.Abstract.CallXE
