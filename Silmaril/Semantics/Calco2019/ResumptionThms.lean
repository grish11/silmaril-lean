module

public import Silmaril.Semantics.Calco2019.Resumption
public import Silmaril.Semantics.Calco2019.KleisliTriple
import Silmaril.Proofs.Semantics.Calco2019.Resumption

/-! # The final-coalgebra construction of the resumption monad -/

public section

universe u v

namespace Silmaril.Calco2019.ParametrizedMonad

open CategoryTheory

variable {C : Type u} [Category.{v} C] (M : ParametrizedMonad C)

/-- A parameter map preserves Kleisli extension. -/
@[reassoc]
theorem parameter_extend {W V X Y : C} (j : W ⟶ V) (g : X ⟶ (M.obj W).obj Y) :
    (M.parameter X).map j ≫ M.extend (W := V) (g ≫ (M.parameter Y).map j) =
      M.extend (W := W) g ≫ (M.parameter Y).map j :=
  Proofs.parameter_extend j g

end Silmaril.Calco2019.ParametrizedMonad

namespace Silmaril.Calco2019.FinalResumptions

open CategoryTheory

variable {C : Type u} [Category.{v} C] {M : ParametrizedMonad C}
  (R : FinalResumptions M) (P : Coproducts C)

@[reassoc]
theorem unfold_spec {X S : C} (b : S ⟶ (M.obj S).obj X) :
    R.unfold b ≫ R.out X = b ≫ (M.parameter X).map (R.unfold b) :=
  Proofs.unfold_spec R b

theorem unfold_unique {X S : C} (b : S ⟶ (M.obj S).obj X) (q : S ⟶ R.obj X)
    (h : q ≫ R.out X = b ≫ (M.parameter X).map q) : q = R.unfold b :=
  Proofs.unfold_unique R b q h

@[reassoc (attr := simp)]
theorem out_roll (X : C) : R.out X ≫ R.roll X = 𝟙 (R.obj X) :=
  Proofs.out_roll R X

@[reassoc (attr := simp)]
theorem roll_out (X : C) : R.roll X ≫ R.out X = 𝟙 ((M.obj (R.obj X)).obj X) :=
  Proofs.roll_out R X

@[reassoc]
theorem extend_spec {X Y : C} (f : X ⟶ R.obj Y) :
    R.extend P f ≫ R.out Y =
      R.out X ≫ (M.parameter X).map (R.extend P f) ≫ M.extend (f ≫ R.out Y) :=
  Proofs.extend_spec R P f

theorem extend_unique {X Y : C} (f : X ⟶ R.obj Y) (k : R.obj X ⟶ R.obj Y)
    (hk : R.IsExtension f k) : k = R.extend P f :=
  Proofs.extend_unique R P f k hk

theorem solve_spec {X Y : C} (f : X ⟶ (M.obj (R.obj (P.sum Y X))).obj Y) :
    R.IsSolution P f (R.solve P f) :=
  (Proofs.solve_spec_unique R P f).1

theorem solve_unique {X Y : C} (f : X ⟶ (M.obj (R.obj (P.sum Y X))).obj Y)
    (g : X ⟶ R.obj Y) (h : R.IsSolution P f g) : g = R.solve P f :=
  (Proofs.solve_spec_unique R P f).2 g h

@[reassoc (attr := simp)]
theorem unit_out (X : C) : R.unit X ≫ R.out X = (M.obj (R.obj X)).η.app X :=
  Proofs.unit_out R X

@[reassoc (attr := simp)]
theorem unit_extend {X Y : C} (f : X ⟶ R.obj Y) : R.unit X ≫ R.extend P f = f :=
  Proofs.unit_extend R P f

@[simp]
theorem extend_unit (X : C) : R.extend P (R.unit X) = 𝟙 (R.obj X) :=
  Proofs.extend_unit R P X

theorem extend_comp {X Y Z : C} (f : X ⟶ R.obj Y) (g : Y ⟶ R.obj Z) :
    R.extend P f ≫ R.extend P g = R.extend P (f ≫ R.extend P g) :=
  Proofs.extend_comp R P f g

/-- The Kleisli triple of the resumption monad. -/
@[expose]
def kleisliTriple : KleisliTriple C where
  obj := R.obj
  unit := R.unit
  extend := R.extend P
  unit_extend := R.unit_extend P
  extend_unit := R.extend_unit P
  extend_comp := R.extend_comp P

/-- The endofunctor induced by the resumption Kleisli triple. -/
@[expose]
def functor : C ⥤ C :=
  (R.kleisliTriple P).functor

/-- The resumption monad of Proposition 23(3). -/
@[expose]
def monad : CategoryTheory.Monad C :=
  (R.kleisliTriple P).monad

/-- The categorical monad's Kleisli extension is the one obtained by finality. -/
theorem monad_extend {X Y : C} (f : X ⟶ R.obj Y) :
    (R.monad P).map f ≫ (R.monad P).μ.app Y = R.extend P f :=
  (R.kleisliTriple P).monad_extend f

end Silmaril.Calco2019.FinalResumptions
