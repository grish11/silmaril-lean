module

public import Silmaril.Wasm.Abstract.XDecomp.Defs
import Silmaril.Proofs.Wasm.Abstract.XDecomp.Basic
import Silmaril.Proofs.Wasm.Abstract.XDecomp.Pend

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

* **Descents are exposed pending calls.** `reachX_iff_pend`: a problem reaches a
  call, of any form, exactly when the exposed body `CallX.denListX` makes that
  call event after events answered by `closedCallX`. So `bodyReachX_iff_exposed`,
  `bodyPathX_iff_exposed`, and divergence of a call through exposed descents
  (`callDivX_iff_exposed`).

**Not yet.** Core 3.0 adequacy (pending the checker extension parameter).
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

open Silmaril.Wasm.Abstract.StoreCall (Answered callOp CallSig)
open Silmaril.Wasm.Abstract.StoreBody (M Res)
open Silmaril.Wasm.Abstract.BodyTrace (Pend)

/-- **Descents through every call form are exposed pending calls.** -/
theorem reachX_iff_pend {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {y : (wasmOShape H).self.Op} :
    ReachX s f stk es y ↔ ∃ cs, Answered Silmaril.Wasm.Abstract.XRecursion.closedCallX cs ∧
      Pend (((Silmaril.Wasm.Abstract.CallX.denListX es f stk : M (CallSig H) H Res).run ⟨s⟩).run)
        cs (callOp y) :=
  ⟨Silmaril.Proofs.Wasm.Abstract.XDecomp.reachX_pend,
    fun ⟨cs, hA, hp⟩ => Silmaril.Proofs.Wasm.Abstract.XDecomp.list_pendX es s f stk cs _ hA hp⟩

theorem bodyReachX_iff_exposed {x y : (wasmOShape H).self.Op} :
    BodyReachX x y ↔ ExposedReachX x y := by
  constructor
  · rintro ⟨fi, fn, hfi, hcode, hr⟩
    exact ⟨fi, fn, hfi, hcode, reachX_iff_pend.1 hr⟩
  · rintro ⟨fi, fn, hfi, hcode, hp⟩
    exact ⟨fi, fn, hfi, hcode, reachX_iff_pend.2 hp⟩

theorem bodyPathX_iff_exposed {x z : (wasmOShape H).self.Op} : BodyPathX x z ↔ ExposedPathX x z := by
  constructor
  · intro h
    induction h with
    | refl x => exact .refl x
    | step h _ ih => exact .step (bodyReachX_iff_exposed.1 h) ih
  · intro h
    induction h with
    | refl x => exact .refl x
    | step h _ ih => exact .step (bodyReachX_iff_exposed.2 h) ih

/-- **Divergence of a call through every call form, on exposed descents.** -/
theorem callDivX_iff_exposed (x : (wasmOShape H).self.Op) :
    CallDivX x ↔ (∃ z, ExposedPathX x z ∧ wasmLocalDivX z) ∨
      ∃ g : Nat → (wasmOShape H).self.Op, g 0 = x ∧ ∀ n, ExposedReachX (g n) (g (n + 1)) := by
  rw [callDivX_iff_path_or_chain]
  constructor
  · rintro (⟨z, hp, hz⟩ | ⟨g, hg0, hg⟩)
    · exact .inl ⟨z, bodyPathX_iff_exposed.1 hp, hz⟩
    · exact .inr ⟨g, hg0, fun n => bodyReachX_iff_exposed.1 (hg n)⟩
  · rintro (⟨z, hp, hz⟩ | ⟨g, hg0, hg⟩)
    · exact .inl ⟨z, bodyPathX_iff_exposed.2 hp, hz⟩
    · exact .inr ⟨g, hg0, fun n => bodyReachX_iff_exposed.2 (hg n)⟩

end Silmaril.Wasm.Abstract.XDecomp
