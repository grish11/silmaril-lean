module

public import Silmaril.Semantics.Calco2019.ExceptionResumption.Interpretation.Thms
import Silmaril.Proofs.Semantics.Calco2019.ExceptionResumptionUniqueness

/-! # Uniqueness of the CALCO 2019 Theorem 28 interpretation -/

public section

universe u v

namespace Silmaril.Calco2019.Exception

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasInitial C] {P : Coproducts C}
  {T S : GuardedElgotMonad P} {H : C ⥤ C}
  (R : FinalResumptions (parametrizedElgot T H).toParametrizedMonad)
  (ξ : GuardedElgotMonadHom P T S) (σ : GuardedTransformation H S)

/-- Any guarded Elgot monad morphism with the two prescribed generator maps
is given by the selected interpretation, componentwise. -/
theorem mediator_unique
    (m : GuardedElgotMonadHom P ((parametrizedElgot T H).resumptionElgotMonad R) S)
    (base : ∀ X, liftBase T H R X ≫ m.hom.app X = ξ.hom.app X)
    (step : ∀ X, liftStep T H R X ≫ m.hom.app X = σ.val.app X)
    (X : C) : m.hom.app X = (mediator R ξ σ X).of :=
  Proofs.mediator_unique T H R ξ σ m base step X

end Silmaril.Calco2019.Exception
