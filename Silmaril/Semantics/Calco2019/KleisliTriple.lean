module

public import Mathlib.CategoryTheory.Monad.Basic

/-! # Kleisli triples for the monads in CALCO 2019, Article 13 -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The unit and Kleisli extension presentation of a categorical monad. -/
structure KleisliTriple (C : Type u) [Category.{v} C] where
  obj : C → C
  unit (X : C) : X ⟶ obj X
  extend {X Y : C} (f : X ⟶ obj Y) : obj X ⟶ obj Y
  unit_extend {X Y : C} (f : X ⟶ obj Y) : unit X ≫ extend f = f
  extend_unit (X : C) : extend (unit X) = 𝟙 (obj X)
  extend_comp {X Y Z : C} (f : X ⟶ obj Y) (g : Y ⟶ obj Z) :
    extend f ≫ extend g = extend (f ≫ extend g)

namespace KleisliTriple

variable (A : KleisliTriple C)

attribute [reassoc (attr := simp)] unit_extend
attribute [simp] extend_unit

def functor : C ⥤ C where
  obj := A.obj
  map f := A.extend (f ≫ A.unit _)
  map_id _ := by simp
  map_comp f g := by simp [extend_comp, Category.assoc]

def monad : CategoryTheory.Monad C where
  toFunctor := A.functor
  η := { app := A.unit, naturality := fun _ _ f => by simp [functor] }
  μ :=
    { app := fun X => A.extend (𝟙 (A.obj X))
      naturality := fun X Y f => by
        change A.extend (A.extend (f ≫ A.unit Y) ≫ A.unit (A.obj Y)) ≫
          A.extend (𝟙 (A.obj Y)) = A.extend (𝟙 (A.obj X)) ≫ A.extend (f ≫ A.unit Y)
        simp [extend_comp, Category.assoc] }
  assoc X := by
    change A.extend (A.extend (𝟙 (A.obj X)) ≫ A.unit (A.obj X)) ≫ A.extend (𝟙 (A.obj X)) =
      A.extend (𝟙 (A.obj (A.obj X))) ≫ A.extend (𝟙 (A.obj X))
    simp [extend_comp, Category.assoc]
  left_unit X := A.unit_extend (𝟙 (A.obj X))
  right_unit X := by
    change A.extend (A.unit X ≫ A.unit (A.obj X)) ≫ A.extend (𝟙 (A.obj X)) = 𝟙 (A.obj X)
    simp [extend_comp, Category.assoc]

theorem monad_extend {X Y : C} (f : X ⟶ A.obj Y) :
    A.monad.map f ≫ A.monad.μ.app Y = A.extend f := by
  change A.extend (f ≫ A.unit (A.obj Y)) ≫ A.extend (𝟙 (A.obj Y)) = _
  simp [extend_comp, Category.assoc]

/-- Recover the Kleisli triple of an existing categorical monad. -/
abbrev ofMonad (T : CategoryTheory.Monad C) : KleisliTriple C where
  obj := T.obj
  unit := T.η.app
  extend f := T.map f ≫ T.μ.app _
  unit_extend f := by
    rw [← T.η.naturality_assoc, T.left_unit]
    exact Category.comp_id f
  extend_unit := T.right_unit
  extend_comp f g := by
    simp only [Category.assoc, Functor.map_comp]
    rw [← T.μ.naturality_assoc g, T.assoc]
    rfl

/-- Component maps preserving the unit and Kleisli extension. -/
structure Hom (B : KleisliTriple C) where
  app (X : C) : A.obj X ⟶ B.obj X
  unit (X : C) : A.unit X ≫ app X = B.unit X
  extend {X Y : C} (f : X ⟶ A.obj Y) :
    A.extend f ≫ app Y = app X ≫ B.extend (f ≫ app Y)

variable {A} in
def Hom.toNatTrans {B : KleisliTriple C} (m : A.Hom B) : A.functor ⟶ B.functor where
  app := m.app
  naturality X Y f := by
    change A.extend (f ≫ A.unit Y) ≫ m.app Y = m.app X ≫ B.extend (f ≫ B.unit Y)
    rw [m.extend, Category.assoc, m.unit]

variable {A} in
def Hom.toMonadHom {B : KleisliTriple C} (m : A.Hom B) : A.monad ⟶ B.monad where
  toNatTrans := m.toNatTrans
  app_η := m.unit
  app_μ X := by
    change A.extend (𝟙 (A.obj X)) ≫ m.app X =
      (A.functor.map (m.app X) ≫ m.app (B.obj X)) ≫ B.extend (𝟙 (B.obj X))
    rw [m.extend, Category.id_comp]
    have natural : A.functor.map (m.app X) ≫ m.app (B.obj X) =
        m.app (A.obj X) ≫ B.functor.map (m.app X) := m.toNatTrans.naturality (m.app X)
    exact ((congrArg (m.app (A.obj X) ≫ ·) (B.monad_extend (m.app X))).symm.trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ B.extend (𝟙 (B.obj X))) natural.symm)))

end KleisliTriple
end Silmaril.Calco2019
