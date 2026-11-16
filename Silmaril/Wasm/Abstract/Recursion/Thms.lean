module

public import Silmaril.Wasm.Abstract.Recursion.Defs
import Silmaril.Proofs.Wasm.Abstract.Recursion.Basic
import Silmaril.Proofs.Wasm.Abstract.Recursion.Core
public import Silmaril.Wasm.Interp.Thms

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

**Against Core 3.0**, on typed, native, arity-checked stores, every profile:

* `core_result_iff_closed`: Core runs of an invocation to a result, final store
  included, are exactly the closed outcomes;
* `behaviours_eq_closed`: the Core behaviours of an invocation are its closed
  outcomes, and divergence *exactly when there is none*. That covers silent
  loops and unbounded recursion alike.

Not covered here: the finer statement that divergence through recursion is an
infinite chain of internal calls (`Shape.closeD`'s coinductive half).
-/

public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- A function looked up through a frame is in the store at its address. -/
theorem funcs_of_func? {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    (h : s.func? f x = some (a, fi)) : s.funcs[a]? = some fi :=
  Silmaril.Proofs.Wasm.Abstract.Recursion.funcs_of_func? h

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

/-- Core 3.0 runs to a result, final store included, are the closed outcomes. -/
theorem core_result_iff_closed {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) (P : Numerics.Profile) (r : Result) (s' : Store H) :
    (∃ c : Config H, Steps P closedHost (invoke s a vs) c ∧ c.code = r.toAdmin ∧ c.store = s') ↔
      ∃ fl, ClosedOutcome s a vs s' fl ∧ flowBeh fl = some r.toBehaviour :=
  Silmaril.Proofs.Wasm.Abstract.Recursion.core_result_iff_closed hs hF hS hok P r s'

/-- **Core 3.0 behaviours are the closed outcomes**, and divergence exactly when
there is none. -/
theorem behaviours_eq_closed {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) (P : Numerics.Profile) :
    behaviours P closedHost s a vs =
      {b | (∃ s' fl, ClosedOutcome s a vs s' fl ∧ flowBeh fl = some b) ∨
        (b = .diverges ∧ ∀ s' fl, ¬ ClosedOutcome s a vs s' fl)} :=
  Silmaril.Proofs.Wasm.Abstract.Recursion.behaviours_eq_closed hs hF hS hok P

end Silmaril.Wasm.Abstract
