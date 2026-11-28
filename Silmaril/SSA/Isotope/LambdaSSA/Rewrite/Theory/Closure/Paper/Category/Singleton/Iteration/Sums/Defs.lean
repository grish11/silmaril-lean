module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Padding.Thms

/-! # Reassociations of exact sums, as isos of default Paper

Each iso is given by case analysis in both directions. The inverse laws
are computed with the injection and copair equations.
-/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Isos on both summands. -/
noncomputable def sumBoth {P Q P' Q' : τ} (i : ofType (Φ := Φ) P ≅ ofType P')
    (j : ofType (Φ := Φ) Q ≅ ofType Q') :
    ofType (Φ := Φ) (Silmaril.coprod P Q) ≅ ofType (Silmaril.coprod P' Q') where
  hom := sumDesc (i.hom ≫ sumInl P' Q') (j.hom ≫ sumInr P' Q')
  inv := sumDesc (i.inv ≫ sumInl P Q) (j.inv ≫ sumInr P Q)
  hom_inv_id := by
    simp only [sumDesc_comp, Category.assoc, sumInl_sumDesc, sumInr_sumDesc, Iso.hom_inv_id_assoc,
      sumDesc_inl_inr]
  inv_hom_id := by
    simp only [sumDesc_comp, Category.assoc, sumInl_sumDesc, sumInr_sumDesc, Iso.inv_hom_id_assoc,
      sumDesc_inl_inr]

/-- `A + B ≅ B + A`. -/
noncomputable def sumSwap (A B : τ) :
    ofType (Φ := Φ) (Silmaril.coprod A B) ≅ ofType (Silmaril.coprod B A) where
  hom := sumDesc (sumInr B A) (sumInl B A)
  inv := sumDesc (sumInr A B) (sumInl A B)
  hom_inv_id := by simp only [sumDesc_comp, sumInl_sumDesc, sumInr_sumDesc, sumDesc_inl_inr]
  inv_hom_id := by simp only [sumDesc_comp, sumInl_sumDesc, sumInr_sumDesc, sumDesc_inl_inr]

/-- `(A + M) + L ≅ A + (M + L)`. -/
noncomputable def sumAssocR (A M L : τ) :
    ofType (Φ := Φ) (Silmaril.coprod (Silmaril.coprod A M) L) ≅
      ofType (Silmaril.coprod A (Silmaril.coprod M L)) where
  hom := sumDesc (sumDesc (sumInl A (Silmaril.coprod M L)) (sumInl M L ≫ sumInr A (Silmaril.coprod M L)))
    (sumInr M L ≫ sumInr A (Silmaril.coprod M L))
  inv := sumDesc (sumInl A M ≫ sumInl (Silmaril.coprod A M) L)
    (sumDesc (sumInr A M ≫ sumInl (Silmaril.coprod A M) L) (sumInr (Silmaril.coprod A M) L))
  hom_inv_id := by
    simp only [sumDesc_comp, Category.assoc, sumInl_sumDesc, sumInr_sumDesc, sumDesc_eta, sumDesc_inl_inr]
  inv_hom_id := by
    simp only [sumDesc_comp, Category.assoc, sumInl_sumDesc, sumInr_sumDesc, sumDesc_eta, sumDesc_inl_inr]

/-- The middle-four interchange `(A + B) + (C + D) ≅ (A + C) + (B + D)`. -/
noncomputable def sumInterchange (A B C D : τ) :
    ofType (Φ := Φ) (Silmaril.coprod (Silmaril.coprod A B) (Silmaril.coprod C D)) ≅
      ofType (Silmaril.coprod (Silmaril.coprod A C) (Silmaril.coprod B D)) where
  hom := sumDesc
    (sumDesc (sumInl A C ≫ sumInl (Silmaril.coprod A C) (Silmaril.coprod B D))
      (sumInl B D ≫ sumInr (Silmaril.coprod A C) (Silmaril.coprod B D)))
    (sumDesc (sumInr A C ≫ sumInl (Silmaril.coprod A C) (Silmaril.coprod B D))
      (sumInr B D ≫ sumInr (Silmaril.coprod A C) (Silmaril.coprod B D)))
  inv := sumDesc
    (sumDesc (sumInl A B ≫ sumInl (Silmaril.coprod A B) (Silmaril.coprod C D))
      (sumInl C D ≫ sumInr (Silmaril.coprod A B) (Silmaril.coprod C D)))
    (sumDesc (sumInr A B ≫ sumInl (Silmaril.coprod A B) (Silmaril.coprod C D))
      (sumInr C D ≫ sumInr (Silmaril.coprod A B) (Silmaril.coprod C D)))
  hom_inv_id := by
    simp only [sumDesc_comp, Category.assoc, sumInl_sumDesc, sumInr_sumDesc, sumDesc_eta, sumDesc_inl_inr]
  inv_hom_id := by
    simp only [sumDesc_comp, Category.assoc, sumInl_sumDesc, sumInr_sumDesc, sumDesc_eta, sumDesc_inl_inr]

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
