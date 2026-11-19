module

public import Silmaril.Wasm.Component.Reference.LegalBoundary.Defs
public import Silmaril.Wasm.Execution.Core.Sim.ExitLift

/-!
# The `core3P` status of a raw Core result (proofs)

`statusP_result`: `Game.statusP P s (.active f r.toAdmin) = .returned (callAndTrapOnThrow r)`
for every raw Core result `r` (values, trap, uncaught exception). The exception case is the
third branch of `statusP` (as `SingleThreaded.status_throw` for `status`); the values case uses
the injectivity of `vals`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.LegalBoundary

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Component.Reference.LegalBoundary

variable {H : Type}

theorem throwing_ne_vals (a : Nat) : ¬ ∃ vs, throwing a = vals vs := by
  rintro ⟨vs, h⟩
  have := congrArg splitVals h
  rw [splitVals_vals] at this
  simp [splitVals, Admin.val?] at this

private theorem trap_ne_vals : ¬ ∃ vs, [Admin.trap] = vals vs := by
  rintro ⟨vs, h⟩
  have := congrArg splitVals h
  rw [splitVals_vals] at this
  simp [splitVals, Admin.val?] at this

theorem statusP_result (P : Numerics.Profile) (s : Store H) (f : Frame) (r : Result) :
    Silmaril.Wasm.Game.statusP P s (.active f r.toAdmin) = .returned (callAndTrapOnThrow r) := by
  cases r with
  | values vs =>
    unfold Silmaril.Wasm.Game.statusP
    dsimp only [Thread.config, Result.toAdmin]
    rw [dite_eq_left ⟨vs, rfl⟩]
    have h : ∃ ws, vals vs = vals ws := ⟨vs, rfl⟩
    rw [Sim.vals_injective h.choose_spec.symm]
    rfl
  | trap =>
    unfold Silmaril.Wasm.Game.statusP
    dsimp only [Thread.config, Result.toAdmin]
    rw [dite_eq_right trap_ne_vals, ite_eq_left rfl]
    rfl
  | throw a =>
    have h2 : throwing a ≠ [.trap] := by simp [throwing]
    unfold Silmaril.Wasm.Game.statusP
    dsimp only [Thread.config, Result.toAdmin]
    rw [dite_eq_right (throwing_ne_vals a), ite_eq_right h2, ite_eq_left ⟨a, rfl⟩]
    rfl

end Silmaril.Proofs.Wasm.Component.Reference.LegalBoundary
