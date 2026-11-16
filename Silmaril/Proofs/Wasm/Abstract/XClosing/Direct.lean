module

public import Silmaril.Wasm.Abstract.XClosing.Defs
public import Silmaril.Wasm.Abstract.XRecursion.Thms
import Silmaril.Proofs.Wasm.Abstract.XClosing.Basic
import Silmaril.Wasm.Abstract.Closing.Thms

/-!
Proofs for `Silmaril.Wasm.Abstract.XClosing.Thms`, the direct part: on code
without extended call forms, logged extended runs are logged native runs
(`evalLX_iff_evalL`), so on stores whose functions are direct the two open
modules agree (`wasmOpenX_eq`), and so do their closures (`close_wasmOpenX_eq`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.XClosing

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.XRecursion Silmaril.Wasm.Abstract.XClosing

variable {H : Type}

theorem evalLX_of_evalL {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (OCall H)} {r : Store H × Frame × Flow} (h : EvalL s f stk es l r) :
    EvalLX s f stk es l r := by
  induction h with
  | nil => exact .nil
  | argsAbort _ hfl ih => exact .argsAbort ih hfl
  | callRet _ hfi hty _ ih₁ ih₂ => exact .callRet ih₁ hfi hty ih₂
  | callThrow _ hfi hty ih => exact .callThrow ih hfi hty
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

theorem evalL_of_evalLX {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (OCall H)} {r : Store H × Frame × Flow} (h : EvalLX s f stk es l r) :
    xFreeL es = true → EvalL s f stk es l r := by
  induction h with
  | nil => intro _; exact .nil
  | argsAbort _ hfl ih =>
    intro hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .argsAbort (ih hx.1.2) hfl
  | callRet _ hfi hty _ ih₁ ih₂ =>
    intro hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .callRet (ih₁ hx.1.2) hfi hty (ih₂ hx.2)
  | callThrow _ hfi hty ih =>
    intro hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .callThrow (ih hx.1.2) hfi hty
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
  | @ifOk s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr fl l₁ l₂ l₃ r _ hb har _ hvs _
      ih₁ ih₂ ih₃ =>
    intro hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .ifOk (ih₁ hx.1.1.1) hb har (ih₂ (by cases b <;> simp [hx.1.1.2, hx.1.2])) hvs (ih₃ hx.2)
  | @ifBrk s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr k l₁ l₂ _ hb har _ ih₁ ih₂ =>
    intro hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .ifBrk (ih₁ hx.1.1.1) hb har (ih₂ (by cases b <;> simp [hx.1.1.2, hx.1.2]))
  | @ifEsc s s₁ s₂ f f₁ f₂ stk stk₁ cv b bt c t el es np nr fl l₁ l₂ _ hb har _ hfl ih₁ ih₂ =>
    intro hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .ifEsc (ih₁ hx.1.1.1) hb har (ih₂ (by cases b <;> simp [hx.1.1.2, hx.1.2])) hfl
  | ifAbort _ hfl ih =>
    intro hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .ifAbort (ih hx.1.1.1) hfl
  | callIndRet => intro hx; simp [xFreeL, xFree, isXCall] at hx
  | callIndThrow => intro hx; simp [xFreeL, xFree, isXCall] at hx
  | callIndRes => intro hx; simp [xFreeL, xFree, isXCall] at hx
  | callRefRet => intro hx; simp [xFreeL, xFree, isXCall] at hx
  | callRefThrow => intro hx; simp [xFreeL, xFree, isXCall] at hx
  | callRefNull => intro hx; simp [xFreeL, xFree, isXCall] at hx
  | tailRet _ hres =>
    intro hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    simp [isXCall_of_tailRes hres] at hx
  | tailThrow _ hres =>
    intro hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    simp [isXCall_of_tailRes hres] at hx
  | tailRes _ hres =>
    intro hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    simp [isXCall_of_tailRes hres] at hx

theorem evalLX_iff_evalL {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    (hx : xFreeL es = true) {l : List (OCall H)} {r : Store H × Frame × Flow} :
    EvalLX s f stk es l r ↔ EvalL s f stk es l r :=
  ⟨fun h => evalL_of_evalLX h hx, evalLX_of_evalL⟩

/-- On a direct store, the open modules agree. -/
theorem wasmOpenX_eq {s : Store H} (hs : StoreXFree s) (a : Nat) (vs : List Val) :
    wasmOpenX a s vs = wasmOpen a s vs := by
  ext x
  constructor
  · rintro ⟨fi, fn, ps, rs, s', f₂, bfl, fl, hfi, hc, hty, d, hx, he⟩
    exact ⟨fi, fn, ps, rs, s', f₂, bfl, fl, hfi, hc, hty,
      (evalLX_iff_evalL (hs a fi fn hfi hc)).1 d, hx, he⟩
  · rintro ⟨fi, fn, ps, rs, s', f₂, bfl, fl, hfi, hc, hty, d, hx, he⟩
    exact ⟨fi, fn, ps, rs, s', f₂, bfl, fl, hfi, hc, hty,
      (evalLX_iff_evalL (hs a fi fn hfi hc)).2 d, hx, he⟩

/-- On a direct store, the closures agree. -/
theorem close_wasmOpenX_eq {s : Store H} (hs : StoreXFree s) (a : Nat) (vs : List Val) :
    Shape.close wasmOpenX a s vs = Shape.close wasmOpen a s vs := by
  rw [close_eqX, Silmaril.Proofs.Wasm.Abstract.Closing.close_eq]
  ext y
  simp only [Silmaril.Proofs.Wasm.Abstract.Closing.toClosed, Set.mem_ofPred_eq, closedCallX_iff hs]

end Silmaril.Proofs.Wasm.Abstract.XClosing
