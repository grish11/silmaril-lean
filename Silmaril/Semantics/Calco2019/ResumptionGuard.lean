module

public import Silmaril.Semantics.Calco2019.Parametrized
public import Silmaril.Semantics.Calco2019.ResumptionThms

/-! # Guarded resumption maps and their iteration -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019

open CategoryTheory

variable {C : Type u} [Category.{v} C] {P : Coproducts C}

/-- Guards for the parameter monads and their preservation along parameter maps. -/
structure ParametrizedMonad.Guards (M : ParametrizedMonad C) (P : Coproducts C) where
  guard (W : C) : MonadGuardedness P (M.obj W)
  preserves {W V : C} (k : W ⟶ V) : MonadGuardedness.Preserves P (guard W) (guard V) (M.map k)

namespace ParametrizedMonad.Guards

variable {M : ParametrizedMonad C} (G : M.Guards P) (R : FinalResumptions M)

abbrev guardedAt (W : C) {X Y Z : C} (f : X ⟶ (M.obj W).obj (P.sum Y Z)) : Prop :=
  (G.guard W).guarded
    (Y := Kleisli.mk (M.obj W) Y) (Z := Kleisli.mk (M.obj W) Z) (kleisliArrow f)

/-- Definition 24. Guardedness is checked at the first observation of a resumption. -/
def ResumptionGuard {X Y Z : C} (f : X ⟶ R.obj (P.sum Y Z)) : Prop :=
  G.guardedAt (R.obj (P.sum Y Z)) (Y := Y) (Z := Z) (f ≫ R.out (P.sum Y Z))

abbrev observedGuard {X Y Z : Kleisli (R.monad P)}
    (f : X ⟶ (P.kleisli (R.monad P)).sum Y Z) : Prop :=
  G.ResumptionGuard R (Y := Y.of) (Z := Z.of) f.of

end ParametrizedMonad.Guards

variable (M : ParametrizedGuardedElgotMonad P) (R : FinalResumptions M.toParametrizedMonad)

namespace ParametrizedGuardedElgotMonad

/-- Forget the chosen iteration and retain the guards of the parameter monads. -/
def toGuards : M.toParametrizedMonad.Guards P where
  guard W := (M.obj W).guard
  preserves k := (M.map k).guarded

/-- Guardedness in the Kleisli category at a particular parameter. -/
abbrev guardedAt (W : C) {X Y Z : C} (f : X ⟶ (M.obj W).monad.obj (P.sum Y Z)) : Prop :=
  M.toGuards.guardedAt W (Y := Y) (Z := Z) f

/-- The inherited guard on resumptions over a guarded Elgot family. -/
def ResumptionGuard {X Y Z : C} (f : X ⟶ R.obj (P.sum Y Z)) : Prop :=
  M.toGuards.ResumptionGuard R (Y := Y) (Z := Z) f

/-- Definition 24 as a predicate on the resumption Kleisli category. -/
abbrev observedGuard {X Y Z : Kleisli (R.monad P)}
    (f : X ⟶ (P.kleisli (R.monad P)).sum Y Z) : Prop :=
  M.toGuards.observedGuard R f

/-- Both nested recursive summands are guarded after pure reassociation. -/
def ResumptionNested {S X Y Z : C} (f : S ⟶ R.obj (P.sum (P.sum X Y) Z)) : Prop :=
  M.ResumptionGuard R (Y := X) (Z := P.sum Y Z) (f ≫ (R.monad P).map P.assoc)

/-- The inner iteration `♦ f` of Theorem 25, in the monad at the fixed resumption parameter. -/
def diamond {X Y : C} (f : X ⟶ R.obj (P.sum Y X)) (hf : M.ResumptionGuard R (Y := Y) (Z := X) f) :
    X ⟶ (M.obj (R.obj (P.sum Y X))).monad.obj Y :=
  ((M.obj (R.obj (P.sum Y X))).iteration.iterate
    (kleisliArrow (f ≫ R.out (P.sum Y X))) hf).of

/-- The solution obtained by first iterating immediate recursive calls and then using finality. -/
def iterateResumption {X Y : C} (f : X ⟶ R.obj (P.sum Y X))
    (hf : M.ResumptionGuard R (Y := Y) (Z := X) f) : X ⟶ R.obj Y :=
  R.solve P (M.diamond R f hf)

/-- Postprocess a successful return and keep recursive calls in the right summand. -/
def naturalityBody {X Y Z : C} (f : X ⟶ R.obj (P.sum Y X)) (g : Y ⟶ R.obj Z) :
    X ⟶ R.obj (P.sum Z X) :=
  f ≫ R.extend P (P.desc (g ≫ (R.monad P).map P.inl) (P.inr ≫ R.unit (P.sum Z X)))

end ParametrizedGuardedElgotMonad
end Silmaril.Calco2019
