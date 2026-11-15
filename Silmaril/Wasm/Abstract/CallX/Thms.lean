module

public import Silmaril.Wasm.Abstract.CallX.Defs

/-!
# Indirect, reference and tail calls: theorems

* `EvalOX.of_evalO` (Defs): every `EvalO C` derivation is an `EvalOX C` one.
* `evalO_of_xFree`, `evalOX_iff_evalO`: on code without the extended call forms
  (`xFreeL`), `EvalOX C` is exactly `EvalO C`. The direct-call part of the
  extended relation is the existing oracle semantics.
-/

public section

namespace Silmaril.Wasm.Abstract.CallX

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel EvalO)

variable {H : Type}

theorem isXCall_of_tailRes {s : Store H} {f : Frame} {i : Instr} {stk : List Val}
    {o : Option (Nat × List Val)} (h : TailRes s f i stk o) : isXCall i = true := by
  cases h <;> rfl

/-- **The direct part is `EvalO`.** On code without the extended call forms an
`EvalOX C` derivation is an `EvalO C` derivation. -/
theorem evalO_of_xFree {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {r : Store H × Frame × Flow} (h : EvalOX C s f stk es r) :
    xFreeL es = true → EvalO C s f stk es r := by
  induction h with
  | nil => intro _; exact .nil
  | argsAbort _ hfl ih =>
    intro hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .argsAbort (ih hx.1.2) hfl
  | callOk _ hfi hty hcall hvs _ ih₁ ih₂ =>
    intro hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .callOk (ih₁ hx.1.2) hfi hty hcall hvs (ih₂ hx.2)
  | callTrap _ hfi hty hcall ih =>
    intro hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .callTrap (ih hx.1.2) hfi hty hcall
  | callThrow _ hfi hty hcall ih =>
    intro hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .callThrow (ih hx.1.2) hfi hty hcall
  | opOk hi _ hflat _ ih₁ ih₂ =>
    intro hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .opOk hi (ih₁ hx.1.2) hflat (ih₂ hx.2)
  | opStop hi _ hflat hfl ih =>
    intro hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .opStop hi (ih hx.1.2) hflat hfl
  | blockOk har _ hvs _ ih₁ ih₂ =>
    intro hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .blockOk har (ih₁ hx.1) hvs (ih₂ hx.2)
  | blockBrk har _ ih =>
    intro hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .blockBrk har (ih hx.1)
  | blockEsc har _ hfl ih =>
    intro hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .blockEsc har (ih hx.1) hfl
  | loopOk har _ _ ih₁ ih₂ =>
    intro hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .loopOk har (ih₁ hx.1) (ih₂ hx.2)
  | loopBack har _ _ ih₁ ih₂ =>
    intro hx
    have hx' := hx
    simp only [xFreeL, xFree, Bool.and_eq_true] at hx'
    exact .loopBack har (ih₁ hx'.1) (ih₂ hx)
  | loopBrk har _ ih =>
    intro hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .loopBrk har (ih hx.1)
  | loopEsc har _ hfl ih =>
    intro hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .loopEsc har (ih hx.1) hfl
  | @ifOk s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr fl r _ hb har _ hvs _ ih₁ ih₂ ih₃ =>
    intro hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .ifOk (ih₁ hx.1.1.1) hb har (ih₂ (by cases b <;> simp [hx.1.1.2, hx.1.2])) hvs (ih₃ hx.2)
  | @ifBrk s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr k _ hb har _ ih₁ ih₂ =>
    intro hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .ifBrk (ih₁ hx.1.1.1) hb har (ih₂ (by cases b <;> simp [hx.1.1.2, hx.1.2]))
  | @ifEsc s s₁ s₂ f f₁ f₂ stk stk₁ cv b bt c t el es np nr fl _ hb har _ hfl ih₁ ih₂ =>
    intro hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .ifEsc (ih₁ hx.1.1.1) hb har (ih₂ (by cases b <;> simp [hx.1.1.2, hx.1.2])) hfl
  | ifAbort _ hfl ih =>
    intro hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .ifAbort (ih hx.1.1.1) hfl
  | callIndOk => intro hx; simp [xFreeL, xFree, isXCall] at hx
  | callIndRes => intro hx; simp [xFreeL, xFree, isXCall] at hx
  | callIndStop => intro hx; simp [xFreeL, xFree, isXCall] at hx
  | callRefOk => intro hx; simp [xFreeL, xFree, isXCall] at hx
  | callRefNull => intro hx; simp [xFreeL, xFree, isXCall] at hx
  | callRefStop => intro hx; simp [xFreeL, xFree, isXCall] at hx
  | tail _ hres =>
    intro hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    simp [isXCall_of_tailRes hres] at hx
  | tailRes _ hres =>
    intro hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    simp [isXCall_of_tailRes hres] at hx

/-- **On code without the extended call forms, the extended relation is
`EvalO`.** -/
theorem evalOX_iff_evalO {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {r : Store H × Frame × Flow} (hx : xFreeL es = true) :
    EvalOX C s f stk es r ↔ EvalO C s f stk es r :=
  ⟨fun h => evalO_of_xFree h hx, EvalOX.of_evalO⟩

end Silmaril.Wasm.Abstract.CallX
