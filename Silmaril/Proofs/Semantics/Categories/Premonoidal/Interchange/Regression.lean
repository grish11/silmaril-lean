module

import Silmaril.Semantics.Categories.Premonoidal.Interchange.Thms

open CategoryTheory PremonoidalCategory
open scoped MonoidalCategory PremonoidalCategory

namespace Silmaril.Proofs.Semantics.Categories.Premonoidal.Interchange

universe u v

variable {C : Type u} [Category.{v} C] [PremonoidalCategory C]

-- Bifunctorial composition would make even an arbitrary effectful arrow central.
example (exchange : ∀ {X Y Z A B D : C} (f : X ⟶ Y) (f' : Y ⟶ Z)
    (g : A ⟶ B) (g' : B ⟶ D),
    (f ⊗ₘ g) ≫ (f' ⊗ₘ g') = (f ≫ f') ⊗ₘ (g ≫ g'))
    {X Y : C} (f : X ⟶ Y) : IsCentral f :=
  ⟨fun g => leftTensor_eq_rightTensor_of_interchange exchange f g,
   fun g => leftTensor_eq_rightTensor_of_interchange exchange g f⟩

section EqualityOrder

local instance (X Y : C) : LE (X ⟶ Y) := ⟨Eq⟩

-- With the equality order, a separately supplied parallel operation still
-- forces the schedules to agree if it preserves both original whiskers.
example (P : ∀ {X Y A B : C}, (X ⟶ Y) → (A ⟶ B) → (X ⊗ A ⟶ Y ⊗ B))
    (right : ∀ {X Y : C} (f : X ⟶ Y) (A : C), P f (𝟙 A) = f ▷ A)
    (left : ∀ (X : C) {A B : C} (g : A ⟶ B), P (𝟙 X) g = X ◁ g)
    (lax : ∀ {X Y Z A B D : C} (f : X ⟶ Y) (f' : Y ⟶ Z)
      (g : A ⟶ B) (g' : B ⟶ D), P f g ≫ P f' g' ≤ P (f ≫ f') (g ≫ g'))
    {X Y A B : C} (f : X ⟶ Y) (g : A ⟶ B) : f ⋉ g = f ⋊ g := by
  obtain ⟨fg, gf⟩ := sequentialTensors_le_of_lax P right left lax f g
  exact Eq.trans fg (Eq.symm gf)

end EqualityOrder

end Silmaril.Proofs.Semantics.Categories.Premonoidal.Interchange
