module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.Factorization.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ThreeCycleFactorization

/-! # A repeating payload cannot pass through a partial phase fold -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle

open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}

local notation "Q" => TypeCategory Seed

/-- The two fold maps compose to the full fold on the underlying coproducts. -/
theorem partialFold_comp_fold (A : Q) (keep : Fin 3) :
    partialFold A keep ≫ coprod.desc (𝟙 A) (𝟙 A) = fold A :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ThreeCycleFactorization.partialFold_comp_fold A keep

/-- A square propagates equality of two phase images around the cycle
at any fixed repeating payload. The intermediate state is arbitrary. -/
theorem collapse_of_shared_phases {A B X D : Q}
    (g : A ⟶ B ⨿ A) (x : X ⟶ A) (repeats : x ≫ g = x ≫ coprod.inr)
    (h : A ⨿ (A ⨿ A) ⟶ D) (exit : B ⟶ D) (next : D ⟶ B ⨿ D)
    (square : step g ≫ coprod.map (𝟙 B) h = h ≫ next) :
    let first := x ≫ coprod.inl ≫ h
    let second := x ≫ (coprod.inl ≫ coprod.inr) ≫ h
    let third := x ≫ (coprod.inr ≫ coprod.inr) ≫ h
    (first = second ∨ second = third ∨ third = first) → first = second ∧ second = third :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ThreeCycleFactorization.collapse_of_shared_phases
    g x repeats h exit next square

/-- When the two retained tags are distinct on the repeating payload,
none of the three partial folds admits an intermediate step. -/
theorem no_partial_fold_square {X A B : Q} (g : A ⟶ B ⨿ A)
    (x : X ⟶ A) (repeats : x ≫ g = x ≫ coprod.inr)
    (distinct : x ≫ (coprod.inl : A ⟶ A ⨿ A) ≠ x ≫ coprod.inr)
    (exit : B ⟶ A ⨿ A) (keep : Fin 3) (next : A ⨿ A ⟶ B ⨿ (A ⨿ A)) :
    step g ≫ coprod.map (𝟙 B) (partialFold A keep) ≠ partialFold A keep ≫ next :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ThreeCycleFactorization.no_partial_fold_square
    g x repeats distinct exit keep next

/-- The full fold is uniform for repeat-only steps even when no partial-fold square exists. -/
theorem iterate_repeat (A B : Q) :
    iterateChosen Seed (step (coprod.inr : A ⟶ B ⨿ A)) =
      fold A ≫ iterateChosen Seed (coprod.inr : A ⟶ B ⨿ A) :=
  (fold_iff_triple Seed (coprod.inr : A ⟶ B ⨿ A)).mpr (by simp [triple])

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle
