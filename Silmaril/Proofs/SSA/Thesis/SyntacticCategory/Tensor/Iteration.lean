module

public import Silmaril.SSA.Thesis.SyntacticCategory.Tensor.Distributivity.Thms

public section

universe u

namespace Silmaril.Thesis.LambdaIter.Syn.SynCat

open CategoryTheory CategoryTheory.Limits

variable {S : Sig.{u}}

theorem iterate'_uniformity_proof {A A' B : SynCat S} (f : A ⟶ B ⨿ A)
    (g : A' ⟶ B ⨿ A') (k : A ⟶ A') (hk : IsPureMor k)
    (square : f ≫ coprod.map (𝟙 B) k = k ≫ g) : iterate' f = k ≫ iterate' g := by
  have changeSum : (copIso B A).inv ≫ copMap (𝟙 B) k =
      coprod.map (𝟙 B) k ≫ (copIso B A').inv := by
    rw [copMap_id_left, copIso_inv_desc]
    apply coprod.hom_ext
    · rw [coprod.inl_desc, coprod.inl_map_assoc, Category.id_comp, coprod_inl_copIso_inv]
    · rw [coprod.inr_desc, coprod.inr_map_assoc, coprod_inr_copIso_inv]
  apply iterate_uniformity' _ _ k hk
  rw [Category.assoc, changeSum, ← Category.assoc, square, Category.assoc]

end Silmaril.Thesis.LambdaIter.Syn.SynCat
