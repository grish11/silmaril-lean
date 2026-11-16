module

public import Silmaril.Wasm.Abstract.CallXP.Thms

/-!
# The closed call relation with pending tail calls (F5)

`closedCallXP` is the least fixpoint of answering every call by running the callee's body in
`CallXP.EvalOXP` and leaving its frame (`CallXP.FrameP`): a tail call made by the callee is answered
only there, outside every handler of the callee, as in Core 3.0.

Theorems in `Silmaril.Wasm.Abstract.XRecursionP.Thms`. New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.XRecursionP

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel)
open Silmaril.Wasm.Abstract.CallXP

variable {H : Type}

/-- One round of answering calls, as a monotone operator. -/
def bodyCallXPOp : CallRel H →o CallRel H where
  toFun := bodyCallXP
  monotone' _ _ hC _ _ _ _ := fun ⟨fi, fn, ps, rs, f₂, s₁, o, h₁, h₂, h₃, h₄, h₅⟩ =>
    ⟨fi, fn, ps, rs, f₂, s₁, o, h₁, h₂, h₃, h₄.mono hC, h₅.mono hC⟩

/-- **The closed call relation with pending tail calls.** -/
def closedCallXP : CallRel H := (bodyCallXPOp (H := H)).lfp

end Silmaril.Wasm.Abstract.XRecursionP
