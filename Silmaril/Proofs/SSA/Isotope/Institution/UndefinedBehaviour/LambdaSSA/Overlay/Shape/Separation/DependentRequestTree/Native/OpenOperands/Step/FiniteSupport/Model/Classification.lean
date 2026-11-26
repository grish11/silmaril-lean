module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Infinite.Thms
import Mathlib.Logic.Function.Iterate

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits)
open CFG.Dependent (Packet)
open Syntax (Payload StatePrimitives)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R : List Syntax.Ty} {σ : Type v}
  {g : Table S R} {a : Payload (R.get g.entry)} {prim : StatePrimitives Φ σ} {p : Packet R} {s : σ}

private theorem external_of_terminal
    (stop : ¬ ∃ q t, (g.head a p).execute prim s = .repeat q t) :
    ∃ o : Outcome Exits.length Unit σ,
      (g.feedback a prim (blockPoint p s)).Ordinary (Feedback.external R Exits o) := by
  rw [g.feedback_step]
  cases step : (g.head a p).execute prim s with
  | exit i selected t =>
    exact ⟨.ret i .unit t, by simp [StateTransition.routed, Behaviour.Ordinary, Behaviour.possible]⟩
  | fault t =>
    exact ⟨.fault t, by simp [StateTransition.routed, Behaviour.Ordinary, Behaviour.possible, Feedback.external]⟩
  | diverge =>
    exact ⟨.diverge, by simp [StateTransition.routed, Behaviour.Ordinary, Behaviour.possible, Feedback.external]⟩
  | «repeat» q t => exact False.elim (stop ⟨q, t, step⟩)

theorem finite_or_infinite (g : Table S R) (a : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ)
    (p : Packet R) (s : σ) :
    (∃ rows stop, FiniteRun g a prim p s rows stop) ∨
      Feedback.Infinite (g.feedback a prim) (blockPoint p s) := by
  classical
  let advance (point : Packet R × σ) : Packet R × σ :=
    match (g.head a point.1).execute prim point.2 with
    | .repeat q t => (q, t)
    | _ => point
  let path (i : Nat) := (advance^[i]) (p, s)
  let continues (i : Nat) := ∃ q t, (g.head a (path i).1).execute prim (path i).2 = .repeat q t
  have follows (i : Nat) (next : continues i) :
      (g.head a (path i).1).execute prim (path i).2 = .repeat (path (i + 1)).1 (path (i + 1)).2 := by
    obtain ⟨q, t, run⟩ := next
    have arrives : path (i + 1) = (q, t) := by
      change (advance^[i + 1]) (p, s) = _
      rw [Function.iterate_succ_apply']
      dsimp only [advance]
      rw [run]
    rw [arrives]
    exact run
  by_cases terminal : ∃ i, ¬ continues i
  · let cut := Nat.find terminal
    have prior (i : Nat) (before : i < cut) : continues i := by
      by_contra stopped
      exact (Nat.not_le_of_lt before) (Nat.find_min' terminal stopped)
    have reaches (i : Nat) (within : i ≤ cut) :
        Feedback.Reaches (g.feedback a prim) (blockPoint p s) (blockPoint (path i).1 (path i).2) := by
      induction i with
      | zero => exact .refl
      | succ i ih =>
        exact (ih (Nat.le_of_succ_le within)).tail ((g.feedback_step_iff a prim _ _ _).mpr
          ⟨_, _, follows i (prior i (Nat.lt_of_succ_le within)), rfl⟩)
    obtain ⟨o, observed⟩ := external_of_terminal (g := g) (a := a) (prim := prim)
      (p := (path cut).1) (s := (path cut).2) (show ¬ continues cut from Nat.find_spec terminal)
    exact .inl (FiniteRun.of_feedback_finite (o := o) ⟨_, reaches cut le_rfl, observed⟩)
  · have repeatAt (i : Nat) : continues i := by
      by_contra stopped
      exact terminal ⟨i, stopped⟩
    exact .inr (GuardedReplay.is_infinite ⟨path, rfl, fun i => follows i (repeatAt i)⟩)

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model
