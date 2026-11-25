module

public import Silmaril.Semantics.Calco2019.InductiveResumption.Defs
public import Silmaril.Semantics.Calco2019.KleisliTriple
import Silmaril.Proofs.Semantics.Calco2019.InductiveResumption

/-! # The inductive resumption monad of CALCO 2019, §1.2 -/

public section

universe u v

namespace Silmaril.Calco2019.InitialResumptions

open CategoryTheory

variable {C : Type u} [Category.{v} C] {M : ParametrizedMonad C}
  (R : InitialResumptions M)

@[reassoc]
theorem fold_spec {X S : C} (a : (M.obj S).obj X ⟶ S) :
    R.roll X ≫ R.fold a = (M.parameter X).map (R.fold a) ≫ a :=
  Proofs.InductiveResumption.fold_spec R a

theorem fold_unique {X S : C} (a : (M.obj S).obj X ⟶ S) (k : R.obj X ⟶ S)
    (hk : R.roll X ≫ k = (M.parameter X).map k ≫ a) : k = R.fold a :=
  Proofs.InductiveResumption.fold_unique R a k hk

@[reassoc (attr := simp)]
theorem out_roll (X : C) : R.out X ≫ R.roll X = 𝟙 (R.obj X) :=
  Proofs.InductiveResumption.out_roll R X

@[reassoc (attr := simp)]
theorem roll_out (X : C) : R.roll X ≫ R.out X = 𝟙 ((M.obj (R.obj X)).obj X) :=
  Proofs.InductiveResumption.roll_out R X

@[reassoc]
theorem extend_spec {X Y : C} (f : X ⟶ R.obj Y) :
    R.roll X ≫ R.extend f =
      (M.parameter X).map (R.extend f) ≫ M.extend (f ≫ R.out Y) ≫ R.roll Y :=
  Proofs.InductiveResumption.extend_spec R f

theorem extend_unique {X Y : C} (f : X ⟶ R.obj Y) (k : R.obj X ⟶ R.obj Y)
    (hk : R.roll X ≫ k = (M.parameter X).map k ≫ M.extend (f ≫ R.out Y) ≫ R.roll Y) :
    k = R.extend f :=
  Proofs.InductiveResumption.extend_unique R f k hk

@[reassoc]
theorem extend_out {X Y : C} (f : X ⟶ R.obj Y) :
    R.extend f ≫ R.out Y =
      R.out X ≫ (M.parameter X).map (R.extend f) ≫ M.extend (f ≫ R.out Y) :=
  Proofs.InductiveResumption.extend_out R f

@[reassoc (attr := simp)]
theorem unit_out (X : C) : R.unit X ≫ R.out X = (M.obj (R.obj X)).η.app X :=
  Proofs.InductiveResumption.unit_out R X

@[reassoc (attr := simp)]
theorem unit_extend {X Y : C} (f : X ⟶ R.obj Y) : R.unit X ≫ R.extend f = f :=
  Proofs.InductiveResumption.unit_extend R f

@[simp]
theorem extend_unit (X : C) : R.extend (R.unit X) = 𝟙 (R.obj X) :=
  Proofs.InductiveResumption.extend_unit R X

theorem extend_comp {X Y Z : C} (f : X ⟶ R.obj Y) (g : Y ⟶ R.obj Z) :
    R.extend f ≫ R.extend g = R.extend (f ≫ R.extend g) :=
  Proofs.InductiveResumption.extend_comp R f g

/-- The inductive resumption unit and extension form a Kleisli triple. -/
@[expose]
def kleisliTriple : KleisliTriple C where
  obj := R.obj
  unit := R.unit
  extend := R.extend
  unit_extend := R.unit_extend
  extend_unit := R.extend_unit
  extend_comp := R.extend_comp

/-- The inductive resumption monad selected by the initial algebras. -/
@[expose]
def monad : CategoryTheory.Monad C :=
  R.kleisliTriple.monad

/-- The monad's Kleisli extension is the initial-algebra fold. -/
theorem monad_extend {X Y : C} (f : X ⟶ R.obj Y) :
    R.monad.map f ≫ R.monad.μ.app Y = R.extend f :=
  R.kleisliTriple.monad_extend f

end Silmaril.Calco2019.InitialResumptions
