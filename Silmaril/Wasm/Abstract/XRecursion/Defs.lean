module

public import Silmaril.Wasm.Abstract.CallX.Defs

/-!
# Closing the extended call forms: recursion (F4, call forms)

`Silmaril.Wasm.Abstract.Recursion` closes `EvalO` by the least fixpoint
`closedCall` of answering calls by running callees. This module does the same
for the extended relation `CallX.EvalOX`, whose call forms (`call_indirect`,
`call_ref`, the tail calls) are answered by the same oracle:
`closedCallX := lfp bodyCallXOp`. Its outcomes are the *finite* derivations of
the recursive extended semantics; divergence is not represented here, and is
not the absence of outcomes on untyped code.

`StoreXFree s`: every function of `s` with native code has no extended call
form. On such stores the closure is `closedCall`
(`Silmaril.Wasm.Abstract.XRecursion.Thms`).
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.XRecursion

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel)
open Silmaril.Wasm.Abstract.CallX

variable {H : Type}

/-- One round of answering calls by running callees in the extended relation:
the code at `a` evaluated by `EvalOX C` in a fresh frame. -/
def bodyCallX (C : CallRel H) : CallRel H := fun s a args out =>
  ∃ (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType) (f₂ : Frame),
    s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
    Validation.DefType.funcType? fi.type = some (ps, rs) ∧
    EvalOX C s (Frame.forCall fi.module args fn.locals) [] (liftInstrs fn.body) (out.1, f₂, out.2)

/-- `EvalOX` is monotone in its oracle. -/
theorem _root_.Silmaril.Wasm.Abstract.CallX.EvalOX.mono {C C' : CallRel H} (hC : C ≤ C')
    {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr} {r : Store H × Frame × Flow}
    (h : EvalOX C s f stk es r) : EvalOX C' s f stk es r := by
  induction h with
  | nil => exact .nil
  | argsAbort _ hfl ih => exact .argsAbort ih hfl
  | callOk _ hfi hty hcall hvs _ ih₁ ih₂ => exact .callOk ih₁ hfi hty (hC _ _ _ _ hcall) hvs ih₂
  | callTrap _ hfi hty hcall ih => exact .callTrap ih hfi hty (hC _ _ _ _ hcall)
  | callThrow _ hfi hty hcall ih => exact .callThrow ih hfi hty (hC _ _ _ _ hcall)
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
  | callIndOk _ hres hfi hty hcall hvs _ ih₁ ih₂ =>
    exact .callIndOk ih₁ hres hfi hty (hC _ _ _ _ hcall) hvs ih₂
  | callIndRes _ hres ih => exact .callIndRes ih hres
  | callIndStop _ hres hfi hty hcall hfl ih => exact .callIndStop ih hres hfi hty (hC _ _ _ _ hcall) hfl
  | callRefOk _ hfi hty hcall hvs _ ih₁ ih₂ => exact .callRefOk ih₁ hfi hty (hC _ _ _ _ hcall) hvs ih₂
  | callRefNull _ ih => exact .callRefNull ih
  | callRefStop _ hfi hty hcall hfl ih => exact .callRefStop ih hfi hty (hC _ _ _ _ hcall) hfl
  | tail _ hres hfi hty hcall hfl ih => exact .tail ih hres hfi hty (hC _ _ _ _ hcall) hfl
  | tailRes _ hres ih => exact .tailRes ih hres

/-- One round of answering calls, as a monotone operator. -/
def bodyCallXOp : CallRel H →o CallRel H where
  toFun := bodyCallX
  monotone' _ _ hC _ _ _ _ := fun ⟨fi, fn, ps, rs, f₂, h₁, h₂, h₃, h₄⟩ =>
    ⟨fi, fn, ps, rs, f₂, h₁, h₂, h₃, h₄.mono hC⟩

/-- **The closed extended call relation**: the least fixpoint of answering
every call form by running its callee. -/
def closedCallX : CallRel H := (bodyCallXOp (H := H)).lfp

/-- The closed outcomes of an invocation in the extended semantics. -/
def ClosedOutcomeX (s : Store H) (a : Nat) (vs : List Val) (s' : Store H) (fl : Flow) : Prop :=
  ∃ (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType) (f₂ : Frame) (bfl : Flow),
    s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
    Validation.DefType.funcType? fi.type = some (ps, rs) ∧
    EvalOX closedCallX s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body)
      (s', f₂, bfl) ∧
    Silmaril.Wasm.Abstract.exitFlow rs.length bfl = some fl

/-- No function of the store with native code uses an extended call form. -/
def StoreXFree (s : Store H) : Prop :=
  ∀ (a : Nat) (fi : FuncInst H) (fn : Func), s.funcs[a]? = some fi → fi.code = .wasm fn →
    xFreeL (liftInstrs fn.body) = true

end Silmaril.Wasm.Abstract.XRecursion
