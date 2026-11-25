module

public import Silmaril.Semantics.Calco2019.ExceptionResumption.Interpretation.Multiplication
import Silmaril.Proofs.Semantics.Calco2019.ExceptionResumptionIteration

/-! # Preservation of iteration in CALCO 2019 Theorem 28 -/

public section

universe u v

namespace Silmaril.Calco2019.Exception

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasInitial C] {P : Coproducts C}
  {T S : GuardedElgotMonad P} {H : C ⥤ C}
  (R : FinalResumptions (parametrizedElgot T H).toParametrizedMonad)
  (ξ : GuardedElgotMonadHom P T S) (σ : GuardedTransformation H S)

/-- Interpreting the two-stage solution of a guarded resumption loop gives the
selected solution of its interpreted body. -/
theorem mediator_iterate {X Y : C} (f : X ⟶ R.obj (P.sum Y X))
    (hf : (parametrizedElgot T H).ResumptionGuard R (Y := Y) (Z := X) f) :
    let J := Kleisli.Adjunction.toKleisli S.monad
    J.map ((parametrizedElgot T H).iterateResumption R f hf) ≫ mediator R ξ σ Y =
      S.iteration.iterate (J.map f ≫ mediator R ξ σ (P.sum Y X))
        (mediator_guard R ξ σ f hf) :=
  Proofs.mediator_iterate R ξ σ f hf

/-- The explicit interpretation preserves guards and their chosen solutions. -/
noncomputable def mediatorHom :
    GuardedElgotMonadHom P ((parametrizedElgot T H).resumptionElgotMonad R) S where
  hom := mediatorMonadHom R ξ σ
  guarded := Proofs.mediator_monad_guard R ξ σ
  iteration := Proofs.mediator_iterate_of R ξ σ

@[simp]
theorem mediatorHom_app (X : C) : (mediatorHom R ξ σ).hom.app X = (mediator R ξ σ X).of := by
  unfold mediatorHom
  exact mediatorMonadHom_app R ξ σ X

end Silmaril.Calco2019.Exception
