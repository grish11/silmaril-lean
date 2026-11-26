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

/-- Read the written cyclic schedule at its first phase. -/
theorem iterate_step_at_first {A B : Q} (g : A ⟶ B ⨿ A) :
    coprod.inl ≫ I (step g) = I (triple g) := by
  rw [Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ThreeCycle.iterate_eq, coprod.inl_desc]

/-- Uniformity for this square is equivalent to iteration being unchanged by grouping three rounds. -/
theorem fold_iff_triple {A B : Q} (g : A ⟶ B ⨿ A) :
    I (step g) = fold A ≫ I g ↔ I (triple g) = I g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ThreeCycle.fold_iff_triple Seed g

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle
