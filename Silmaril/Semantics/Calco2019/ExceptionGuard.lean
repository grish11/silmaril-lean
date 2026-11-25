module

public import Silmaril.Semantics.Calco2019.ExceptionThms
public import Silmaril.Semantics.Calco2019.Parametrized

/-! # Guardedness for the exception parameter of Example 22 -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019.Exception

open CategoryTheory

variable {C : Type u} [Category.{v} C] (P : Coproducts C)

/-- Move exceptions into the result summand, keeping recursive calls on the right. -/
def rearrange (E : C) {Y Z : C} : P.sum (P.sum Y Z) E ⟶ P.sum (P.sum Y E) Z :=
  P.desc (P.desc (P.inl ≫ P.inl) P.inr) (P.inr ≫ P.inl)

/-- The guardedness predicate of Example 22 depends only on the guard of the base monad. -/
def guardOf {T : CategoryTheory.Monad C} (G : MonadGuardedness P T) (E : C) {X Y Z : C}
    (f : X ⟶ T.obj (P.sum (P.sum Y Z) E)) : Prop :=
  G.guarded (Y := Kleisli.mk T (P.sum Y E)) (Z := Kleisli.mk T Z)
    (kleisliArrow (f ≫ T.map (rearrange P E)))

/-- The same predicate on the exception Kleisli category. -/
abbrev kleisliGuardOf {T : CategoryTheory.Monad C} (G : MonadGuardedness P T) (E : C)
    {X Y Z : Kleisli ((family P T).obj E)}
    (f : X ⟶ (P.kleisli ((family P T).obj E)).sum Y Z) : Prop :=
  guardOf P G E (Y := Y.of) (Z := Z.of) f.of

/-- The guard of an exception parameter over a guarded Elgot base. -/
def Guard (T : GuardedElgotMonad P) (E : C) {X Y Z : C}
    (f : X ⟶ T.monad.obj (P.sum (P.sum Y Z) E)) : Prop :=
  guardOf P T.guard E (Y := Y) (Z := Z) f

abbrev kleisliGuard (T : GuardedElgotMonad P) (E : C)
    {X Y Z : Kleisli ((family P T.monad).obj E)}
    (f : X ⟶ (P.kleisli ((family P T.monad).obj E)).sum Y Z) : Prop :=
  kleisliGuardOf P T.guard E f

/-- Solve the normalized loop in the original guarded Elgot monad. -/
def iterate (T : GuardedElgotMonad P) (E : C) {X Y : C}
    (f : X ⟶ T.monad.obj (P.sum (P.sum Y X) E))
    (hf : Guard P T E (Y := Y) (Z := X) f) : X ⟶ T.monad.obj (P.sum Y E) :=
  (T.iteration.iterate (kleisliArrow (f ≫ T.monad.map (rearrange P E))) hf).of

end Silmaril.Calco2019.Exception
