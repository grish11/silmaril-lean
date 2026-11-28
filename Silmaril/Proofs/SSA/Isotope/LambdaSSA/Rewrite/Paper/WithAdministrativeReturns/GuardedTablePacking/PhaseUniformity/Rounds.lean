module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Rounds.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.Thms
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonPhases
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonRounds

/-! # Every round count unrolls with phase uniformity

Default Paper reduces the loop on `n + 1` rounds to a cycle of phases.
The one use of the added seed closes that cycle along the phase fold.
-/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity (Step)
open Paper.Extension.Singleton (projection ofRegion_eq_iff iterateChosen projectStep exists_projectStep
  iterateChosen_projectStep)
open Paper.Extension.Singleton.Rounds
open Paper.TypeCategory (ofType iterate phaseType phaseFold exists_ofRegion)
open Semantics.Categorical (roundsStep)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "N" => Step (τ := τ) (Φ := Φ) pe

set_option backward.isDefEq.respectTransparency false

/-- The added equations, read in the quotient category: the loop of a
step on the phases is the fold followed by the loop on the state, when the
fold is a simulation in default Paper. -/
theorem fold_uniform (k : Nat) {A B : τ}
    (f : ofType (Φ := Φ) (phaseType A k) ⟶ ofType B ⨿ ofType (phaseType A k))
    (g : ofType (Φ := Φ) A ⟶ ofType B ⨿ ofType A)
    (square : f ≫ coprod.map (𝟙 _) (phaseFold A k) = phaseFold A k ≫ g) :
    (projection N).map (iterate f) = (projection N).map (phaseFold A k ≫ iterate g) := by
  obtain ⟨r, hr, left⟩ := exists_ofRegion (iterate f)
  obtain ⟨s, hs, right⟩ := exists_ofRegion (phaseFold A k ≫ iterate g)
  rw [left, right]
  exact (ofRegion_eq_iff N hr hs).2
    (.extra hr.hasType hs.hasType (.inr (.fold k f g square hr hs left.symm right.symm)))

theorem roundsLaw (n : Nat) : RoundsLaw (Step (τ := τ) (Φ := Φ) pe) n := by
  intro X Y g
  obtain ⟨h, rfl⟩ := exists_projectStep N g
  obtain ⟨start, cycle, startFold, square, enters⟩ :=
    SingletonPhases.exists_cycle (Φ := Φ) (show τ from X.as) (B := (show τ from Y.as)) h n
  calc
    iterateChosen N (roundsStep (projectStep N h) n) =
        iterateChosen N (projectStep N (roundsStep h n)) :=
      congrArg (iterateChosen N) (SingletonRounds.projectStep_roundsStep N h n).symm
    _ = (projection N).map (iterate (roundsStep h n)) := iterateChosen_projectStep N _
    _ = (projection N).map start ≫ (projection N).map (iterate cycle) :=
      (congrArg (projection N).map enters).trans ((projection N).map_comp _ _)
    _ = (projection N).map start ≫ (projection N).map (phaseFold _ n ≫ iterate h) :=
      congrArg ((projection N).map start ≫ ·) (fold_uniform pe n cycle h square)
    _ = (projection N).map ((start ≫ phaseFold _ n) ≫ iterate h) := by
      rw [← Functor.map_comp, Category.assoc]
    _ = (projection N).map (iterate h) := by rw [startFold, Category.id_comp]
    _ = iterateChosen N (projectStep N h) := (iterateChosen_projectStep N h).symm

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity
