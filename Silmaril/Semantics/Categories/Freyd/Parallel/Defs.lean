module

public import Silmaril.Semantics.Categories.Thms

/-! # Directed parallel pairing for Freyd models -/

@[expose] public section

namespace CategoryTheory.FreydCategory

open scoped MonoidalCategory

universe u v u' v'

variable {V : Type u} {C : Type v} [Category.{u'} V] [Category.{v'} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [∀ X Y : C, Preorder (X ⟶ Y)]

/-- An opt-in parallel operation on computation arrows between interpreted value objects.
Its domain and codomain are already transported along the chosen Freyd tensor comparisons.
Composition is directed in general and exact for a stage consisting of two pure arrows.
Ambient composition monotonicity is supplied separately where needed. -/
structure OrderedParallel (J : V ⥤ C) [FreydCategory J] where
  tensor {X Y A B : V} : (J.obj X ⟶ J.obj Y) → (J.obj A ⟶ J.obj B) →
    (J.obj (X ⊗ A) ⟶ J.obj (Y ⊗ B))
  tensor_mono {X Y A B : V} {f f' : J.obj X ⟶ J.obj Y} {g g' : J.obj A ⟶ J.obj B} :
    f ≤ f' → g ≤ g' → tensor f g ≤ tensor f' g'
  lax_comp {X Y Z A B D : V} (f : J.obj X ⟶ J.obj Y) (g : J.obj A ⟶ J.obj B)
      (h : J.obj Y ⟶ J.obj Z) (k : J.obj B ⟶ J.obj D) :
    tensor f g ≫ tensor h k ≤ tensor (f ≫ h) (g ≫ k)
  whiskerLeft (X : V) {A B : V} (g : J.obj A ⟶ J.obj B) :
    tensor (𝟙 (J.obj X)) g =
      (Functor.StrongPremonoidal.tensorIso (J := J) X A).inv ≫ J.obj X ◁ g ≫
        (Functor.StrongPremonoidal.tensorIso (J := J) X B).hom
  whiskerRight {X Y : V} (f : J.obj X ⟶ J.obj Y) (A : V) :
    tensor f (𝟙 (J.obj A)) =
      (Functor.StrongPremonoidal.tensorIso (J := J) X A).inv ≫ f ▷ J.obj A ≫
        (Functor.StrongPremonoidal.tensorIso (J := J) Y A).hom
  pure_pre {X Y Z A B D : V} (f : X ⟶ Y) (g : A ⟶ B)
      (h : J.obj Y ⟶ J.obj Z) (k : J.obj B ⟶ J.obj D) :
    tensor (J.map f) (J.map g) ≫ tensor h k = tensor (J.map f ≫ h) (J.map g ≫ k)
  pure_post {X Y Z A B D : V} (f : J.obj X ⟶ J.obj Y) (g : J.obj A ⟶ J.obj B)
      (h : Y ⟶ Z) (k : B ⟶ D) :
    tensor f g ≫ tensor (J.map h) (J.map k) = tensor (f ≫ J.map h) (g ≫ J.map k)
  map_associator {X Y A B S T : V} (f : J.obj X ⟶ J.obj Y)
      (g : J.obj A ⟶ J.obj B) (h : J.obj S ⟶ J.obj T) :
    tensor (tensor f g) h ≫ J.map (α_ Y B T).hom =
      J.map (α_ X A S).hom ≫ tensor f (tensor g h)
  map_braiding {X Y A B : V} (f : J.obj X ⟶ J.obj Y) (g : J.obj A ⟶ J.obj B) :
    tensor f g ≫ J.map (BraidedCategory.braiding Y B).hom =
      J.map (BraidedCategory.braiding X A).hom ≫ tensor g f
  map_leftUnitor {X Y : V} (f : J.obj X ⟶ J.obj Y) :
    tensor (𝟙 (J.obj (𝟙_ V))) f ≫ J.map (λ_ Y).hom = J.map (λ_ X).hom ≫ f
  map_rightUnitor {X Y : V} (f : J.obj X ⟶ J.obj Y) :
    tensor f (𝟙 (J.obj (𝟙_ V))) ≫ J.map (ρ_ Y).hom = J.map (ρ_ X).hom ≫ f

namespace OrderedParallel

variable {J : V ⥤ C} [FreydCategory J]

/-- Share only the input values. The two branches return a product in branch order. -/
noncomputable def par (P : OrderedParallel J) {R A B : V}
    (f : J.obj R ⟶ J.obj A) (g : J.obj R ⟶ J.obj B) :
    J.obj R ⟶ J.obj (A ⊗ B) :=
  J.map (CartesianMonoidalCategory.lift (𝟙 R) (𝟙 R)) ≫ P.tensor f g

end OrderedParallel
end CategoryTheory.FreydCategory
