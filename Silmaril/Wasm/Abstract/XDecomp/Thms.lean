module

public import Silmaril.Wasm.Abstract.XDecomp.Defs
import Silmaril.Proofs.Wasm.Abstract.XDecomp.Basic

/-!
# Decomposing divergence through every call form: theorems

* `evalDivX_decomp`: a diverging problem diverges within its function, or
  reaches (`ReachX`) a diverging call; `reach_evalDivX` is the converse.
* **Divergence of a call, exactly** (`callDivX_iff_path_or_chain`): a call
  diverges in the extended recursive semantics (`XDiverge.EvalDivX` of its body)
  exactly when finitely many descents (`BodyPathX`) reach a locally diverging
  call (`wasmLocalDivX`), or an infinite chain of descents (`BodyReachX`) starts
  at it. Every call form is a descent; any store.

This is the positive divergence of #319/#322 extended structurally, not the
absence of outcomes. Answers exclude it (`XDiverge.not_funDivX_of_closedOutcomeX`).

**Not yet.** The correspondence with exposed descents of `CallX.denListX`, and
Core 3.0 adequacy (pending the checker extension parameter).
-/

public section

namespace Silmaril.Wasm.Abstract.XDecomp

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (wasmOShape)
open Silmaril.Wasm.Abstract.XDiverge

variable {H : Type}

theorem reach_evalDivX {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {y : (wasmOShape H).self.Op} (h : ReachX s f stk es y) (hy : CallDivX y) : EvalDivX s f stk es :=
  Silmaril.Proofs.Wasm.Abstract.XDecomp.reach_evalDivX h hy

/-- **A diverging problem diverges within its function or reaches a diverging
call.** -/
theorem evalDivX_decomp {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    (h : EvalDivX s f stk es) : LocalDivX s f stk es ∨ ∃ y, ReachX s f stk es y ∧ CallDivX y :=
  Silmaril.Proofs.Wasm.Abstract.XDecomp.evalDivX_decomp h

/-- **Divergence of a call, through every call form, exactly.** -/
theorem callDivX_iff_path_or_chain (x : (wasmOShape H).self.Op) :
    CallDivX x ↔ (∃ z, BodyPathX x z ∧ wasmLocalDivX z) ∨
      ∃ g : Nat → (wasmOShape H).self.Op, g 0 = x ∧ ∀ n, BodyReachX (g n) (g (n + 1)) := by
  constructor
  · exact Silmaril.Proofs.Wasm.Abstract.XDecomp.callDivX_path_or_chain
  · rintro (⟨z, hp, hz⟩ | ⟨g, rfl, hg⟩)
    · exact Silmaril.Proofs.Wasm.Abstract.XDecomp.callDivX_of_path hp hz
    · exact Silmaril.Proofs.Wasm.Abstract.XDecomp.callDivX_of_chain hg

end Silmaril.Wasm.Abstract.XDecomp
