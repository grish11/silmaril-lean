module

public import Silmaril.Semantics.Categories.Freyd.Parallel.Defs

public section

namespace CategoryTheory.FreydCategory.OrderedParallel

open CartesianMonoidalCategory
open scoped MonoidalCategory

universe u v u' v'

variable {V : Type u} {C : Type v} [Category.{u'} V] [Category.{v'} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [∀ X Y : C, Preorder (X ⟶ Y)]
  {J : V ⥤ C} [FreydCategory J] (P : OrderedParallel J)

private theorem tensor_whiskerLeft_map (X : V) {A B : V} (g : A ⟶ B) :
    P.tensor (𝟙 (J.obj X)) (J.map g) = J.map (X ◁ g) := by
  rw [P.whiskerLeft, Functor.StrongPremonoidal.tensor_naturality_right, Iso.inv_hom_id_assoc]

private theorem tensor_whiskerRight_map {X Y : V} (f : X ⟶ Y) (A : V) :
    P.tensor (J.map f) (𝟙 (J.obj A)) = J.map (f ▷ A) := by
  rw [P.whiskerRight, Functor.StrongPremonoidal.tensor_naturality_left, Iso.inv_hom_id_assoc]

theorem tensor_maps_proof {X Y A B : V} (f : X ⟶ Y) (g : A ⟶ B) :
    P.tensor (J.map f) (J.map g) = J.map (f ⊗ₘ g) := by
  rw [MonoidalCategory.tensorHom_def, J.map_comp, ← tensor_whiskerRight_map P,
    ← tensor_whiskerLeft_map P]
  simpa only [Functor.map_id, Category.comp_id, Category.id_comp] using
    (P.pure_pre f (𝟙 A) (𝟙 (J.obj Y)) (J.map g)).symm

private theorem tensor_pre {X Y Z A B D : V} (f : X ⟶ Y) (g : A ⟶ B)
    (h : J.obj Y ⟶ J.obj Z) (k : J.obj B ⟶ J.obj D) :
    P.tensor (J.map f ≫ h) (J.map g ≫ k) = J.map (f ⊗ₘ g) ≫ P.tensor h k := by
  rw [← P.pure_pre, tensor_maps_proof]

theorem par_reindex_proof {R S A B : V} (k : S ⟶ R) (f : J.obj R ⟶ J.obj A)
    (g : J.obj R ⟶ J.obj B) :
    J.map k ≫ P.par f g = P.par (J.map k ≫ f) (J.map k ≫ g) := by
  simp only [par, tensor_pre P, ← J.map_comp_assoc, comp_lift, lift_map, Category.comp_id,
    Category.id_comp]

theorem par_postmap_proof {R A B X Y : V} (f : J.obj R ⟶ J.obj A) (g : J.obj R ⟶ J.obj B)
    (k : A ⟶ X) (l : B ⟶ Y) :
    P.par f g ≫ J.map (k ⊗ₘ l) = P.par (f ≫ J.map k) (g ≫ J.map l) := by
  rw [par, par, Category.assoc, ← tensor_maps_proof P, P.pure_post]

theorem par_maps_proof {R A B : V} (f : R ⟶ A) (g : R ⟶ B) :
    P.par (J.map f) (J.map g) = J.map (lift f g) := by
  simp only [par, tensor_maps_proof, ← J.map_comp, lift_map, Category.id_comp]

theorem par_swap_proof {R A B : V} (f : J.obj R ⟶ J.obj A) (g : J.obj R ⟶ J.obj B) :
    P.par f g ≫ J.map (BraidedCategory.braiding A B).hom = P.par g f := by
  simp only [par, Category.assoc, P.map_braiding, ← J.map_comp_assoc, lift_braiding_hom]

theorem par_assoc_proof {R A B D : V} (f : J.obj R ⟶ J.obj A) (g : J.obj R ⟶ J.obj B)
    (h : J.obj R ⟶ J.obj D) :
    P.par (P.par f g) h ≫ J.map (α_ A B D).hom = P.par f (P.par g h) := by
  let diag : R ⟶ R ⊗ R := lift (𝟙 R) (𝟙 R)
  have left : P.tensor (J.map diag ≫ P.tensor f g) h =
      J.map (diag ⊗ₘ 𝟙 R) ≫ P.tensor (P.tensor f g) h := by
    simpa only [Functor.map_id, Category.id_comp] using tensor_pre P diag (𝟙 R) (P.tensor f g) h
  have right : P.tensor f (J.map diag ≫ P.tensor g h) =
      J.map (𝟙 R ⊗ₘ diag) ≫ P.tensor f (P.tensor g h) := by
    simpa only [Functor.map_id, Category.id_comp] using tensor_pre P (𝟙 R) diag f (P.tensor g h)
  simp only [par, diag, left, right, Category.assoc, P.map_associator, ← J.map_comp_assoc,
    lift_map, Category.id_comp, Category.comp_id, lift_lift_associator_hom]

theorem par_unit_left_proof {R A : V} (f : J.obj R ⟶ J.obj A) :
    P.par (J.map (toUnit R)) f ≫ J.map (λ_ A).hom = f := by
  have left : P.tensor (J.map (toUnit R)) f =
      J.map (toUnit R ⊗ₘ 𝟙 R) ≫ P.tensor (𝟙 (J.obj (𝟙_ V))) f := by
    simpa only [Functor.map_id, Category.id_comp, Category.comp_id] using
      tensor_pre P (toUnit R) (𝟙 R) (𝟙 (J.obj (𝟙_ V))) f
  simp only [par, left, Category.assoc, P.map_leftUnitor, ← J.map_comp_assoc, lift_map,
    Category.id_comp, lift_leftUnitor_hom, Functor.map_id]

theorem par_unit_right_proof {R A : V} (f : J.obj R ⟶ J.obj A) :
    P.par f (J.map (toUnit R)) ≫ J.map (ρ_ A).hom = f := by
  have right : P.tensor f (J.map (toUnit R)) =
      J.map (𝟙 R ⊗ₘ toUnit R) ≫ P.tensor f (𝟙 (J.obj (𝟙_ V))) := by
    simpa only [Functor.map_id, Category.id_comp, Category.comp_id] using
      tensor_pre P (𝟙 R) (toUnit R) f (𝟙 (J.obj (𝟙_ V)))
  simp only [par, right, Category.assoc, P.map_rightUnitor, ← J.map_comp_assoc, lift_map,
    Category.id_comp, lift_rightUnitor_hom, Functor.map_id]

end CategoryTheory.FreydCategory.OrderedParallel
