module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Defs

/-! # Two blocks with feedback inside and between them -/

@[expose] public section

universe v u

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits

variable (C : Type u) [Category.{v} C] [HasBinaryCoproducts C]

/-- What block elimination uses: an iterator with the fixpoint, naturality
and codiagonal laws, one sum of a left and a right block, and uniformity of
the iterator along its two injections. -/
structure BlockSystem where
  iter : ∀ {X Y : C}, (X ⟶ Y ⨿ X) → (X ⟶ Y)
  fixpoint : ∀ {X Y : C} (f : X ⟶ Y ⨿ X), iter f = f ≫ coprod.desc (𝟙 Y) (iter f)
  naturality : ∀ {X Y Z : C} (f : X ⟶ Y ⨿ X) (g : Y ⟶ Z),
    iter f ≫ g = iter (f ≫ coprod.map g (𝟙 X))
  codiagonal : ∀ {X Y : C} (f : X ⟶ (Y ⨿ X) ⨿ X),
    iter (iter f) = iter (f ≫ coprod.desc (𝟙 (Y ⨿ X)) coprod.inr)
  left : C
  right : C
  sum : C
  inl : left ⟶ sum
  inr : right ⟶ sum
  desc {T : C} : (left ⟶ T) → (right ⟶ T) → (sum ⟶ T)
  inl_desc : ∀ {T : C} (u : left ⟶ T) (v : right ⟶ T), inl ≫ desc u v = u
  inr_desc : ∀ {T : C} (u : left ⟶ T) (v : right ⟶ T), inr ≫ desc u v = v
  ext : ∀ {T : C} {f g : sum ⟶ T}, inl ≫ f = inl ≫ g → inr ≫ f = inr ≫ g → f = g
  uniform_inl : ∀ {B : C} (f : left ⟶ B ⨿ left) (g : sum ⟶ B ⨿ sum),
    f ≫ coprod.map (𝟙 B) inl = inl ≫ g → iter f = inl ≫ iter g
  uniform_inr : ∀ {B : C} (f : right ⟶ B ⨿ right) (g : sum ⟶ B ⨿ sum),
    f ≫ coprod.map (𝟙 B) inr = inr ≫ g → iter f = inr ≫ iter g

variable {C}

/-- A row exits, repeats into the left block, or enters the right block. -/
noncomputable def BlockSystem.route (S : BlockSystem C) (Y : C) :
    (Y ⨿ S.left) ⨿ S.right ⟶ Y ⨿ S.sum :=
  coprod.desc (coprod.map (𝟙 Y) S.inl) (S.inr ≫ coprod.inr)

/-- The joined step of a left row and a right row. Each may exit, go to
the left block, or go to the right block. -/
noncomputable def BlockSystem.joined (S : BlockSystem C) {Y : C}
    (r : S.left ⟶ (Y ⨿ S.left) ⨿ S.right) (c : S.right ⟶ (Y ⨿ S.left) ⨿ S.right) :
    S.sum ⟶ Y ⨿ S.sum :=
  S.desc (r ≫ S.route Y) (c ≫ S.route Y)

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
