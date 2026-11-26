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

end CategoryTheory.PremonoidalCategory
