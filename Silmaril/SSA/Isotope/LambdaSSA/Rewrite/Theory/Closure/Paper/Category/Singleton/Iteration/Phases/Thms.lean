module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Phases.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Rounds.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonPhases

/-! # Rounds become a cycle of phases in default Paper

Default Paper has every ingredient of the phase argument except uniformity
along the phase fold: fixpoint, naturality and codiagonal of guarded
iteration, and uniformity along the constructor injections of exact sums.
-/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits
open Semantics.Categorical (roundsStep)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- The loop on `n + 1` rounds of a step enters a cycle on `n + 1` phases
of its state, and the phase fold is a simulation of that cycle onto one
round. All three equations hold in default Paper. -/
theorem exists_phaseCycle (A : τ) {B : τ} (h : ofType (Φ := Φ) A ⟶ ofType B ⨿ ofType A) (n : Nat) :
    ∃ (start : ofType (Φ := Φ) A ⟶ ofType (phaseType A n))
      (cycle : ofType (Φ := Φ) (phaseType A n) ⟶ ofType B ⨿ ofType (phaseType A n)),
      start ≫ phaseFold A n = 𝟙 _ ∧
      cycle ≫ coprod.map (𝟙 _) (phaseFold A n) = phaseFold A n ≫ h ∧
      iterate (roundsStep h n) = start ≫ iterate cycle :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonPhases.exists_cycle A h n

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
