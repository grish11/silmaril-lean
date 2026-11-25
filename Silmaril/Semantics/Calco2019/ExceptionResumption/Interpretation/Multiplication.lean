module

public import Silmaril.Semantics.Calco2019.ExceptionResumption.Interpretation.Thms
import Silmaril.Proofs.Semantics.Calco2019.ExceptionResumptionMultiplication

/-! # The monad morphism of CALCO 2019 Theorem 28 -/

public section

universe u v

namespace Silmaril.Calco2019.Exception

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasInitial C] {P : Coproducts C}
  {T S : GuardedElgotMonad P} {H : C ⥤ C}
  (R : FinalResumptions (parametrizedElgot T H).toParametrizedMonad)
  (ξ : GuardedElgotMonadHom P T S) (σ : GuardedTransformation H S)

/-- Observing an extended resumption interprets an immediate return with the
continuation body and forwards suspended states through the extension. -/
theorem mediatorBody_extend {X Y : C} (f : X ⟶ R.obj Y) :
    let J := Kleisli.Adjunction.toKleisli S.monad
    let K := P.kleisli S.monad
    J.map (R.extend P f) ≫ mediatorBody R ξ σ Y =
      mediatorBody R ξ σ X ≫ K.desc (J.map f ≫ mediatorBody R ξ σ Y)
        (J.map (R.extend P f) ≫ K.inr) :=
  Proofs.mediatorBody_extend R ξ σ f

/-- Interpreting a resumption Kleisli extension is the extension of its interpreted continuation. -/
theorem mediator_extend {X Y : C} (f : X ⟶ R.obj Y) :
    (Kleisli.Adjunction.toKleisli S.monad).map (R.extend P f) ≫ mediator R ξ σ Y =
      mediator R ξ σ X ≫ ((Kleisli.Adjunction.toKleisli S.monad).map f ≫ mediator R ξ σ Y) :=
  Proofs.mediator_extend R ξ σ f

/-- The interpretation of Theorem 28 preserves the resumption monad's unit and multiplication. -/
noncomputable def mediatorMonadHom : R.monad P ⟶ S.monad where
  app X := (mediator R ξ σ X).of
  naturality _ _ f := Proofs.mediator_natural_of R ξ σ f
  app_η := Proofs.mediator_unit_of R ξ σ
  app_μ := Proofs.mediator_mul R ξ σ

@[simp]
theorem mediatorMonadHom_app (X : C) :
    (mediatorMonadHom R ξ σ).app X = (mediator R ξ σ X).of := by
  unfold mediatorMonadHom
  rfl

end Silmaril.Calco2019.Exception
