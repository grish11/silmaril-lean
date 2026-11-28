module

public import Silmaril.Semantics.Categories.Thms

/-! # Interchange for a premonoidal tensor -/

public section

namespace CategoryTheory.PremonoidalCategory

open scoped MonoidalCategory PremonoidalCategory

universe u v

variable {C : Type u} [Category.{v} C] [PremonoidalCategory C]

/-- Bifunctorial composition for the existing tensor forces the two whiskered
sequences to agree on every pair of arrows. -/
theorem leftTensor_eq_rightTensor_of_interchange
    (interchange : ∀ {X Y Z A B D : C} (f : X ⟶ Y) (f' : Y ⟶ Z)
      (g : A ⟶ B) (g' : B ⟶ D),
      (f ⊗ₘ g) ≫ (f' ⊗ₘ g') = (f ≫ f') ⊗ₘ (g ≫ g'))
    {X Y A B : C} (f : X ⟶ Y) (g : A ⟶ B) : f ⋉ g = f ⋊ g := by
  simpa [PremonoidalCategory.tensorHom_def, leftTensor, rightTensor] using
    (interchange (𝟙 X) f g (𝟙 B)).symm

/-- A lax parallel operation extending the existing whiskers admits both
sequential schedules. Only the two composition comparisons with identities
are needed. -/
theorem sequentialTensors_le_of_lax
    [∀ X Y : C, LE (X ⟶ Y)]
    (P : ∀ {X Y A B : C}, (X ⟶ Y) → (A ⟶ B) → (X ⊗ A ⟶ Y ⊗ B))
    (right : ∀ {X Y : C} (f : X ⟶ Y) (A : C), P f (𝟙 A) = f ▷ A)
    (left : ∀ (X : C) {A B : C} (g : A ⟶ B), P (𝟙 X) g = X ◁ g)
    (lax : ∀ {X Y Z A B D : C} (f : X ⟶ Y) (f' : Y ⟶ Z)
      (g : A ⟶ B) (g' : B ⟶ D), P f g ≫ P f' g' ≤ P (f ≫ f') (g ≫ g'))
    {X Y A B : C} (f : X ⟶ Y) (g : A ⟶ B) : f ⋉ g ≤ P f g ∧ f ⋊ g ≤ P f g := by
  constructor
  · simpa only [right, left, Category.comp_id, Category.id_comp, leftTensor] using
      lax f (𝟙 Y) (𝟙 A) g
  · simpa only [right, left, Category.comp_id, Category.id_comp, rightTensor] using
      lax (𝟙 X) f g (𝟙 B)

end CategoryTheory.PremonoidalCategory
