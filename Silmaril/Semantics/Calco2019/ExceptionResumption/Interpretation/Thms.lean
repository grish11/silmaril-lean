module

public import Silmaril.Semantics.Calco2019.ExceptionResumption.Interpretation.Defs
import Silmaril.Proofs.Semantics.Calco2019.ExceptionResumptionInterpretation

/-! # The interpretation used in the free-extension theorem -/

public section

universe u v

namespace Silmaril.Calco2019.Exception

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasInitial C] {P : Coproducts C}
  {T S : GuardedElgotMonad P} {H : C ⥤ C}
  (R : FinalResumptions (parametrizedElgot T H).toParametrizedMonad)
  (ξ : GuardedElgotMonadHom P T S) (σ : GuardedTransformation H S)

local notation "Q" => S.monad
local notation "K" => P.kleisli Q
local notation "J" => Kleisli.Adjunction.toKleisli Q

theorem mediatorBody_guarded (X : C) :
    S.guard.guarded (Y := Kleisli.mk Q X) (Z := Kleisli.mk Q (R.obj X)) (mediatorBody R ξ σ X) :=
  Proofs.mediatorBody_guarded R ξ σ X

/-- The component specified by Theorem 28 is the selected solution of the
interpretation body. -/
@[expose]
noncomputable def mediator (X : C) : Kleisli.mk Q (R.obj X) ⟶ Kleisli.mk Q X :=
  S.iteration.iterate (mediatorBody R ξ σ X) (mediatorBody_guarded R ξ σ X)

theorem mediator_unfold (X : C) :
    mediator R ξ σ X =
      kleisliArrow (R.out X ≫ ξ.hom.app (P.sum X (H.obj (R.obj X)))) ≫
        (K).desc (𝟙 (Kleisli.mk Q X)) (kleisliArrow (σ.val.app (R.obj X)) ≫ mediator R ξ σ X) :=
  Proofs.mediator_unfold R ξ σ X

theorem mediator_guard {A Y Z : C} (f : A ⟶ R.obj (P.sum Y Z))
    (hf : (parametrizedElgot T H).ResumptionGuard R (Y := Y) (Z := Z) f) :
    S.guard.guarded (Y := Kleisli.mk Q Y) (Z := Kleisli.mk Q Z)
      ((J).map f ≫ mediator R ξ σ (P.sum Y Z)) :=
  Proofs.mediator_guard R ξ σ f hf

theorem mediator_base (X : C) :
    (J).map (liftBase T H R X) ≫ mediator R ξ σ X = kleisliArrow (ξ.hom.app X) :=
  Proofs.mediator_base R ξ σ X

theorem mediator_unit (X : C) :
    (J).map (R.unit X) ≫ mediator R ξ σ X = 𝟙 (Kleisli.mk Q X) :=
  Proofs.mediator_unit R ξ σ X

theorem mediator_step (X : C) :
    (J).map (liftStep T H R X) ≫ mediator R ξ σ X = kleisliArrow (σ.val.app X) :=
  Proofs.mediator_step R ξ σ X

theorem mediator_natural {X Y : C} (f : X ⟶ Y) :
    (J).map ((R.monad P).map f) ≫ mediator R ξ σ Y =
      mediator R ξ σ X ≫ (J).map f :=
  Proofs.mediator_natural R ξ σ f

end Silmaril.Calco2019.Exception
