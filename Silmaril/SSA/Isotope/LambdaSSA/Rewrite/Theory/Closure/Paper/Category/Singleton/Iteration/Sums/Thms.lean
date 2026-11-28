module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Sums.Defs

/-! # Case analysis through the reassociations, and splittings of a sum

A pair `μ : M → Z`, `ℓ : L → Z` splits `Z` when `[μ, ℓ]` is an iso:
`ℓ` is a summand of `Z` and `μ` is its complement. The three lemmas
here build every splitting of a right-nested sum at one of its summands.
-/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

theorem sumBoth_desc {P Q P' Q' T : τ} (i : ofType (Φ := Φ) P ≅ ofType P') (j : ofType (Φ := Φ) Q ≅ ofType Q')
    (a : ofType (Φ := Φ) P' ⟶ ofType T) (b : ofType (Φ := Φ) Q' ⟶ ofType T) :
    (sumBoth i j).hom ≫ sumDesc a b = sumDesc (i.hom ≫ a) (j.hom ≫ b) := by
  simp only [sumBoth, sumDesc_comp, Category.assoc, sumInl_sumDesc, sumInr_sumDesc]

theorem sumInterchange_desc {A B C D T : τ} (a : ofType (Φ := Φ) A ⟶ ofType T) (b : ofType (Φ := Φ) B ⟶ ofType T)
    (c : ofType (Φ := Φ) C ⟶ ofType T) (d : ofType (Φ := Φ) D ⟶ ofType T) :
    (sumInterchange A B C D).hom ≫ sumDesc (sumDesc a c) (sumDesc b d) =
      sumDesc (sumDesc a b) (sumDesc c d) := by
  simp only [sumInterchange, sumDesc_comp, Category.assoc, sumInl_sumDesc, sumInr_sumDesc]

/-- The first summand, with the second as its complement. -/
theorem split_first (A B : τ) : IsIso (sumDesc (sumInr (Φ := Φ) A B) (sumInl A B)) :=
  (sumSwap B A).isIso_hom

/-- The second of two summands, with the first as its complement. -/
theorem split_second (A B : τ) : IsIso (sumDesc (sumInl (Φ := Φ) A B) (𝟙 _ ≫ sumInr A B)) := by
  rw [Category.id_comp, sumDesc_inl_inr]
  infer_instance

/-- A splitting of `Z` gives one of `A + Z` at the same summand. -/
theorem split_under (A : τ) {M L Z : τ} (μ : ofType (Φ := Φ) M ⟶ ofType Z) (ℓ : ofType (Φ := Φ) L ⟶ ofType Z)
    (split : IsIso (sumDesc μ ℓ)) :
    IsIso (sumDesc (sumDesc (sumInl A Z) (μ ≫ sumInr A Z)) (ℓ ≫ sumInr A Z)) := by
  have e : sumDesc (sumDesc (sumInl A Z) (μ ≫ sumInr A Z)) (ℓ ≫ sumInr A Z) =
      (sumAssocR A M L).hom ≫ (sumBoth (Iso.refl _) (asIso (sumDesc μ ℓ))).hom := by
    simp only [sumAssocR, sumBoth, sumDesc_comp, Category.assoc, sumInl_sumDesc, sumInr_sumDesc,
      Iso.refl_hom, Category.id_comp, asIso_hom]
  rw [e]
  infer_instance

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
