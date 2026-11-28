module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ThreeCycle

/-! # The three-copy fold square and the three-round iteration equation -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle

open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed
local notation "I" => iterateChosen Seed

/-- The cyclic source and the one-round target commute with the fold in the quotient. -/
theorem square {A B : Q} (g : A ⟶ B ⨿ A) :
    step g ≫ coprod.map (𝟙 B) (fold A) = fold A ≫ g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ThreeCycle.square Seed g

/-- Eliminate two phases while retaining ordered exits in all three rows. -/
theorem iterate_cycleRows {A B : Q} (first middle last : A ⟶ B ⨿ A) :
    let batch := I (batchRows first middle last)
    I (cycleRows first middle last) = coprod.desc batch
      (coprod.desc ((middle ≫ coprod.desc coprod.inl last) ≫ coprod.desc (𝟙 B) batch)
        (last ≫ coprod.desc (𝟙 B) batch)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ThreeCycle.iterate_cycleRows Seed first middle last

/-- A comparison of the first-phase batches lifts to all phases when the
two suffix rows have commuting squares for the same retained map. -/
theorem uniformity_of_cycleRows {A D B : Q} (h : A ⟶ D)
    (first middle last : A ⟶ B ⨿ A) (first' middle' last' : D ⟶ B ⨿ D)
    (middleSquare : middle ≫ coprod.map (𝟙 B) h = h ≫ middle')
    (lastSquare : last ≫ coprod.map (𝟙 B) h = h ≫ last')
    (batch : I (batchRows first middle last) =
      h ≫ I (batchRows first' middle' last')) :
    I (cycleRows first middle last) =
      coprod.map h (coprod.map h h) ≫ I (cycleRows first' middle' last') :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ThreeCycle.uniformity_of_cycleRows
    Seed h first middle last first' middle' last' middleSquare lastSquare batch

/-- Read the written cyclic schedule at its first phase. -/
theorem iterate_step_at_first {A B : Q} (g : A ⟶ B ⨿ A) :
    coprod.inl ≫ I (step g) = I (triple g) := by
  rw [Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ThreeCycle.iterate_eq, coprod.inl_desc]

/-- Uniformity for this square is equivalent to iteration being unchanged by grouping three rounds. -/
theorem fold_iff_triple {A B : Q} (g : A ⟶ B ⨿ A) :
    I (step g) = fold A ≫ I g ↔ I (triple g) = I g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ThreeCycle.fold_iff_triple Seed g

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle
