module

public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Defs

public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.FreydCategory

open PremonoidalCategory
open CartesianMonoidalCategory (snd toUnit)
open scoped MonoidalCategory

private theorem central_of_left {C : Type u₂} [Category.{v₂} C]
    [PremonoidalCategory C] [SymmetricPremonoidalCategory C] {X Y : C} (a : X ⟶ Y)
    (h : ∀ {A B : C} (f : A ⟶ B), a ▷ A ≫ Y ◁ f = X ◁ f ≫ a ▷ B) :
    IsCentral a := by
  constructor
  · exact h
  · intro A B f
    change f ▷ X ≫ B ◁ a = A ◁ a ≫ f ▷ Y
    apply (cancel_mono (BraidedPremonoidalCategory.braiding B Y).hom).1
    simp only [Category.assoc, BraidedPremonoidalCategory.naturality_right,
      BraidedPremonoidalCategory.naturality_left, BraidedPremonoidalCategory.naturality_right_assoc,
      BraidedPremonoidalCategory.naturality_left_assoc, h f]

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  (J : V ⥤ C) [FreydCategory J]

local notation "U" => Functor.StrongPremonoidal.unitIso (J := J)
local notation "T" => Functor.StrongPremonoidal.tensorIso (J := J)

@[reassoc]
private theorem map_snd (R A : V) :
    (T R A).hom ≫ J.map (snd R A) =
      (J.map (toUnit R) ≫ (U).inv) ▷ J.obj A ≫ (λ_ (J.obj A)).hom := by
  rw [← CartesianMonoidalCategory.whiskerRight_toUnit_comp_leftUnitor_hom,
    J.map_comp, ← Category.assoc, ← Functor.StrongPremonoidal.tensor_naturality_left,
    Category.assoc, comp_whiskerRight, Category.assoc]
  have e := Functor.StrongPremonoidal.left_unitality (J := J) A
  rw [← e, ← comp_whiskerRight_assoc (U).inv (U).hom, (U).inv_hom_id]
  simp

theorem whiskerLeft_snd_proof (h : IsCentral (U).hom) (R : V) {A B : V}
    (f : J.obj A ⟶ J.obj B) :
    (T R A).inv ≫ J.obj R ◁ f ≫ (T R B).hom ≫ J.map (snd R B) =
      J.map (snd R A) ≫ f := by
  have central := (image_central J (toUnit R)).comp (IsCentral.inv U h)
  have slide := central.1 f
  change (J.map (toUnit R) ≫ (U).inv) ▷ J.obj A ≫ 𝟙_ C ◁ f =
    J.obj R ◁ f ≫ (J.map (toUnit R) ≫ (U).inv) ▷ J.obj B at slide
  rw [map_snd, ← Category.assoc _ _ ((λ_ (J.obj B)).hom), ← slide,
    Category.assoc, leftUnitor_naturality, ← map_snd_assoc]
  simp

theorem centralUnit_of_whiskerLeft_snd_proof
    (h : ∀ {A B : V} (f : J.obj A ⟶ J.obj B),
      (T (𝟙_ V) A).inv ≫ J.obj (𝟙_ V) ◁ f ≫
        (T (𝟙_ V) B).hom ≫ J.map (snd (𝟙_ V) B) = J.map (snd (𝟙_ V) A) ≫ f) :
    CentralUnit J := by
  have unit : toUnit (𝟙_ V) = 𝟙 _ := CartesianMonoidalCategory.toUnit_unique _ _
  have proj (A : V) : J.map (snd (𝟙_ V) A) =
      (T (𝟙_ V) A).inv ≫ (U).inv ▷ J.obj A ≫ (λ_ (J.obj A)).hom := by
    rw [← Iso.inv_hom_id_assoc (T (𝟙_ V) A) (J.map (snd (𝟙_ V) A)),
      map_snd, unit, J.map_id, Category.id_comp]
  have inverse : IsCentral (U).inv := by
    apply central_of_left
    intro X Y f
    obtain ⟨A, rfl⟩ := (obj_bijective (J := J)).2 X
    obtain ⟨B, rfl⟩ := (obj_bijective (J := J)).2 Y
    have e := h f
    rw [map_snd, unit, J.map_id, Category.id_comp, proj, Category.assoc,
      Category.assoc, ← leftUnitor_naturality] at e
    apply (cancel_mono (λ_ (J.obj B)).hom).1
    apply (cancel_epi (T (𝟙_ V) A).inv).1
    simpa only [Category.assoc] using e.symm
  exact ⟨IsCentral.inv (U).symm inverse⟩

end CategoryTheory.FreydCategory
