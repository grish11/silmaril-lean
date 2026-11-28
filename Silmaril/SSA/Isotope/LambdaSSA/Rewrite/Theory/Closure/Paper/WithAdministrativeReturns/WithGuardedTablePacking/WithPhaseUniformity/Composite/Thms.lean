module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Classes.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Composite

/-! # Folding several duplicated classes: one overall square

No seed is added.

## Which squares are needed

For two classes `A` and `B`, each duplicated `n + 1` times, one equation
of default Paper suffices: the sum of the two class folds is a simulation
of the whole table onto the folded table (`pair_fold`). The table step is
an arbitrary arrow. Its rows may repeat inside a class and across the
classes, and different duplicates of one class may jump to different
duplicates of the other.

The proof does not fold the classes one after the other. It reassociates
the interleaved duplicates into phases of the pair `A + B` by an iso of
default Paper, uses rolling for that iso, and applies the total-fold seed
once at the state type `A + B`.

## The sequential route

Folding `B` first with `partial_fold_feedback` needs a row
`c₁ : B → (Y + A-duplicates) + B` and the equation
`c ≫ (id + phaseFold) = phaseFold ≫ c₁` in default Paper. That equation
forces every duplicate of `B` to jump to the same duplicate of `A`. Such
an intermediate table need not exist, and `pair_fold` does not ask for
one. That such a row cannot exist for a particular table is not proved
in Lean.

## What is not covered

* Classes with different numbers of duplicates are treated in
  `Composite.Padding`, for sizes that differ by one.
* Other layouts of the state sum and more than two classes. By
  `fold_simulation_iso` each needs only an iso of default Paper from its
  state sum to phases of the folded state type. For an arbitrary finite
  surjection with equal fibres that iso is a permutation of a nested sum,
  which is not constructed here.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity

open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory (ofType iterate phaseType phaseFold pairPhases pairFold)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε) {X Z Y : τ} (n : Nat)

/-- Reduction: if default Paper enters a table on phases of `Z` through
`e`, and the fold is a simulation of that table onto `T`, then the loop is
`e`, the fold, and the loop of `T`. Both premises are equations of
default Paper. -/
theorem fold_simulation_through (e : ofType (Φ := Φ) X ⟶ ofType (phaseType Z n))
    (J : ofType (Φ := Φ) X ⟶ ofType Y ⨿ ofType X)
    (G : ofType (Φ := Φ) (phaseType Z n) ⟶ ofType Y ⨿ ofType (phaseType Z n))
    (T : ofType (Φ := Φ) Z ⟶ ofType Y ⨿ ofType Z)
    (enter : iterate J = e ≫ iterate G)
    (square : G ≫ coprod.map (𝟙 _) (phaseFold Z n) = phaseFold Z n ≫ T) :
    (projection pe).map (iterate J) = (projection pe).map (e ≫ phaseFold Z n ≫ iterate T) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.through
    pe n e J G T enter square

/-- The composite simulation theorem. A state map that is a total fold up
to an iso of default Paper is uniform, from one overall square. -/
theorem fold_simulation_iso (ψ : ofType (Φ := Φ) X ≅ ofType (phaseType Z n))
    (J : ofType (Φ := Φ) X ⟶ ofType Y ⨿ ofType X) (T : ofType (Φ := Φ) Z ⟶ ofType Y ⨿ ofType Z)
    (square : J ≫ coprod.map (𝟙 _) (ψ.hom ≫ phaseFold Z n) = (ψ.hom ≫ phaseFold Z n) ≫ T) :
    (projection pe).map (iterate J) = (projection pe).map ((ψ.hom ≫ phaseFold Z n) ≫ iterate T) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.iso_fold
    pe n ψ J T square

/-- Two independently duplicated classes fold together, from the one
square for the sum of their folds. -/
theorem pair_fold (A B : τ)
    (J : ofType (Φ := Φ) (pairPhases A B n) ⟶ ofType Y ⨿ ofType (pairPhases A B n))
    (T : ofType (Φ := Φ) (Silmaril.coprod A B) ⟶ ofType Y ⨿ ofType (Silmaril.coprod A B))
    (square : J ≫ coprod.map (𝟙 _) (pairFold A B n) = pairFold A B n ≫ T) :
    (projection pe).map (iterate J) = (projection pe).map (pairFold A B n ≫ iterate T) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.pair_fold
    pe n A B J T square

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity
