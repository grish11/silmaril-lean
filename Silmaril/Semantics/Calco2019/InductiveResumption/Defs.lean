module

public import Silmaril.Semantics.Calco2019.Resumption

/-! # Inductive resumptions of parametrized monads -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019

open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor

variable {C : Type u} [Category.{v} C]

/-- The initial-algebra hypothesis of the inductive resumption construction. -/
structure InitialResumptions (M : ParametrizedMonad C) where
  algebra (X : C) : Algebra (M.parameter X)
  initial (X : C) : IsInitial (algebra X)

namespace InitialResumptions

variable {M : ParametrizedMonad C} (R : InitialResumptions M)

abbrev obj (X : C) : C := (R.algebra X).a
abbrev roll (X : C) : (M.obj (R.obj X)).obj X ⟶ R.obj X := (R.algebra X).str

/-- The inverse of the initial-algebra constructor. -/
def out (X : C) : R.obj X ⟶ (M.obj (R.obj X)).obj X :=
  Algebra.Initial.strInv (R.initial X)

/-- The canonical map into an algebra for the endofunctor at result object `X`. -/
def fold {X S : C} (a : (M.obj S).obj X ⟶ S) : R.obj X ⟶ S :=
  ((R.initial X).to (⟨S, a⟩ : Algebra (M.parameter X))).f

/-- An immediate return. -/
def unit (X : C) : X ⟶ R.obj X :=
  (M.obj (R.obj X)).η.app X ≫ R.roll X

/-- Interpret a continuation at the parameter of the target algebra. -/
def extensionAlgebra {X Y : C} (f : X ⟶ R.obj Y) : (M.obj (R.obj Y)).obj X ⟶ R.obj Y :=
  M.extend (f ≫ R.out Y) ≫ R.roll Y

/-- The Kleisli extension is the fold into the continuation algebra. -/
def extend {X Y : C} (f : X ⟶ R.obj Y) : R.obj X ⟶ R.obj Y :=
  R.fold (R.extensionAlgebra f)

end InitialResumptions
end Silmaril.Calco2019
