module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.Thms

/-! # Factorization along a split state inclusion -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SplitImageUniformity

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

open CategoryTheory CategoryTheory.Limits

theorem uniformity_of_split_image (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
    {A B D : TypeCategory Seed} (h : A ⟶ D) (back : D ⟶ A)
    (section_id : h ≫ back = 𝟙 A) (f : A ⟶ B ⨿ A) (g : D ⟶ B ⨿ D)
    (comm : f ≫ coprod.map (𝟙 B) h = h ≫ g)
    (image : g ≫ coprod.map (𝟙 B) (back ≫ h) = g) :
    iterateChosen Seed f = h ≫ iterateChosen Seed g := by
  apply uniformity_of_factorization Seed h f g (g ≫ coprod.map (𝟙 B) back)
  · rw [← Category.assoc, ← comm, Category.assoc, coprod.map_map, Category.id_comp, section_id]
    simp
  · rw [Category.assoc, coprod.map_map, Category.id_comp, image]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SplitImageUniformity
