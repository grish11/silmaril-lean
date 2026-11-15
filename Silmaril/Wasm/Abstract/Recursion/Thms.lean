module

public import Silmaril.Wasm.Abstract.Recursion.Defs
import Silmaril.Proofs.Wasm.Abstract.Recursion.Basic

/-!
# Recursion through internal calls, exposed and closed: theorems

For **terminating** runs, closing the open semantics by least fixpoint is the
recursive semantics:

* `closedCall_eq`: the least fixpoint of "answer calls by running callees"
  is exactly the callee relation of the recursive big-step semantics `Eval`.
* `evalO_closed_iff`: the open semantics with internal calls answered by that
  closure is `Eval`.
* `closedCall_fixpoint`: the closure answers each call by running the callee's
  body with the closure.

`Eval` is Core 3.0-adequate with stores on native stores
(`Silmaril.Wasm.Interp.native_store_adequacy`, via `run`), so closing agrees
with Core 3.0 recursion on terminating runs. Not covered here: divergence
through unbounded recursion (no finite derivation). It needs `Shape.closeD`'s
coinductive half and Core 3.0 `Step` inversion for `call`/frames.
-/

public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- Closing is the recursive callee relation. -/
theorem closedCall_eq : (closedCall : CallRel H) = evalCall :=
  Silmaril.Proofs.Wasm.Abstract.Recursion.closedCall_eq

/-- The open semantics answered by the closure is the recursive semantics. -/
theorem evalO_closed_iff {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} : EvalO closedCall s f stk es r ↔ Eval s f stk es r :=
  Silmaril.Proofs.Wasm.Abstract.Recursion.evalO_closed_iff

/-- The closure is a fixpoint of answering calls by running callees. -/
theorem closedCall_fixpoint : (closedCall : CallRel H) = bodyCall closedCall :=
  Silmaril.Proofs.Wasm.Abstract.Recursion.closedCall_eq_bodyCall

end Silmaril.Wasm.Abstract
