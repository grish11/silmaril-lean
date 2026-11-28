module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralSquareFactorization

open CategoryTheory CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
  {A D E B : C} (h : A ⟶ D) (k : D ⟶ E)
  (f : A ⟶ B ⨿ A) (g : E ⟶ B ⨿ E)
  (square : f ≫ coprod.map (𝟙 B) (h ≫ k) = (h ≫ k) ≫ g)

include square in
theorem intermediate_iff_of_section (s : D ⟶ A) (hs : s ≫ h = 𝟙 D) :
    (∃! m : D ⟶ B ⨿ D,
      f ≫ coprod.map (𝟙 B) h = h ≫ m ∧ m ≫ coprod.map (𝟙 B) k = k ≫ g) ↔
    f ≫ coprod.map (𝟙 B) h = (h ≫ s) ≫ f ≫ coprod.map (𝟙 B) h := by
  constructor
  · rintro ⟨m, ⟨left, _⟩, _⟩
    rw [Category.assoc, left, ← Category.assoc s, hs, Category.id_comp]
  · intro invariant
    refine ⟨s ≫ f ≫ coprod.map (𝟙 B) h, ⟨?_, ?_⟩, ?_⟩
    · simpa only [Category.assoc] using invariant
    · simp only [Category.assoc, coprod.map_map, Category.id_comp]
      rw [square, Category.assoc, ← Category.assoc s h, hs, Category.id_comp]
    · intro m hm
      rw [hm.1, ← Category.assoc s h, hs, Category.id_comp]

include square in
theorem intermediate_of_section_of_retraction (s : D ⟶ A) (hs : s ≫ h = 𝟙 D)
    (r : E ⟶ D) (hr : k ≫ r = 𝟙 D) :
    ∃! m : D ⟶ B ⨿ D,
      f ≫ coprod.map (𝟙 B) h = h ≫ m ∧ m ≫ coprod.map (𝟙 B) k = k ≫ g := by
  apply (intermediate_iff_of_section h k f g square s hs).mpr
  have reduced : f ≫ coprod.map (𝟙 B) h = (h ≫ k) ≫ g ≫ coprod.map (𝟙 B) r := by
    simpa only [Category.assoc, coprod.map_map, Category.id_comp, ← Category.assoc h k r,
      hr, Category.comp_id] using congrArg (· ≫ coprod.map (𝟙 B) r) square
  rw [reduced]
  simp only [Category.assoc, ← Category.assoc s h, hs, Category.id_comp]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralSquareFactorization
