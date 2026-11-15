module

public import Silmaril.Wasm.Abstract.CallXE.Thms

/-!
# The closed call relation with exceptions (F5)

As `XRecursion.closedCallX` for `CallX.EvalOX`, `closedCallXE` is the least fixpoint of answering
every call by running the callee's body in `CallXE.EvalOXE`: a callee may throw, catch and rethrow,
and its answer may be a thrown exception (`.throw a`), which the caller propagates or catches.

Theorems in `Silmaril.Wasm.Abstract.XRecursionE.Thms`. New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.XRecursionE

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel)
open Silmaril.Wasm.Abstract.CallXE

variable {H : Type}

/-- One round of answering calls by running callees in the relation with exceptions: the code at
`a` evaluated by `EvalOXE C` in a fresh frame. -/
def bodyCallXE (C : CallRel H) : CallRel H := fun s a args out =>
  ∃ (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType) (f₂ : Frame),
    s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
    Validation.DefType.funcType? fi.type = some (ps, rs) ∧
    EvalOXE C s (Frame.forCall fi.module args fn.locals) [] (liftInstrs fn.body) (out.1, f₂, out.2)

/-- One round of answering calls, as a monotone operator. -/
def bodyCallXEOp : CallRel H →o CallRel H where
  toFun := bodyCallXE
  monotone' _ _ hC _ _ _ _ := fun ⟨fi, fn, ps, rs, f₂, h₁, h₂, h₃, h₄⟩ =>
    ⟨fi, fn, ps, rs, f₂, h₁, h₂, h₃, h₄.mono hC⟩

/-- **The closed call relation with exceptions**: the least fixpoint of answering every call by
running its callee. -/
def closedCallXE : CallRel H := (bodyCallXEOp (H := H)).lfp

end Silmaril.Wasm.Abstract.XRecursionE
