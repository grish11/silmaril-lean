module

public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.Independence.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.CounterSemiringIndependence

/-! # A Conway operator violating the two-state identity -/

public section

universe u

namespace Silmaril.Calco2019.Guardedness

open CategoryTheory

universe v

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}

/-- Identifying the two alternating states commutes with one unfolding. -/
theorem binaryCycle_fold_square {X Y : K} (f : X ⟶ P.sum Y X) :
    P.desc (𝟙 X) (𝟙 X) ≫ f =
      binaryCycleBody f ≫ P.map (𝟙 Y) (P.desc (𝟙 X) (𝟙 X)) :=
  Proofs.CounterSemiringIndependence.fold_square f

theorem Fixpoints.binaryCycleIdentity_of_fold {F : G.Fixpoints}
    (h : ∀ X, F.UniformAt (P.desc (𝟙 X) (𝟙 X))) : F.BinaryCycleIdentity :=
  fun {X _} f hf hc => (h X f (binaryCycleBody f) hf hc (binaryCycle_fold_square f)).symm

end Silmaril.Calco2019.Guardedness

namespace Silmaril.Calco2019.CounterSemiring.FiniteMatrix

open CategoryTheory Guardedness

theorem iterate_apply {U B : Object.{u}} (f : U ⟶ coproducts.sum B U)
    (i : U.carrier) (b : B.carrier) :
    conway.iterate f True.intro i b = networkDagger (fun x y => f x y) i b :=
  Proofs.CounterSemiringIndependence.iterate_apply f i b

/-- The one-state body, expanded to an alternating pair, refutes the binary
commutative equation in this Conway model. -/
theorem oneBody_fails_binaryCycle :
    conway.iterate (binaryCycleBody oneBody) True.intro ≠
      coproducts.desc (𝟙 one) (𝟙 one) ≫ conway.iterate oneBody True.intro :=
  Proofs.CounterSemiringIndependence.fails_oneBody_cycle

/-- Running the one-state body twice before taking feedback changes the
iteration in this Conway model. -/
theorem oneBody_fails_doubling :
    conway.iterate (oneBody ≫ coproducts.desc coproducts.inl oneBody) True.intro ≠
      conway.iterate oneBody True.intro :=
  Proofs.CounterSemiringIndependence.fails_oneBody_doubling

/-- The full Conway equations do not entail the commutative identity of the binary cycle. -/
theorem conway_fails_binaryCycle : ¬ conway.{0}.toFixpoints.BinaryCycleIdentity :=
  Proofs.CounterSemiringIndependence.fails_cycle

end Silmaril.Calco2019.CounterSemiring.FiniteMatrix

namespace Silmaril.Calco2019.PointedCpo

open OmegaCompletePartialOrder Silmaril.Semantics.Domain

/-- With least-fixed-point semantics, the two alternating equations both
have the solution of the original one-state equation. -/
theorem alternating_fix {D : Type u} [OmegaCompletePartialOrder D] [OrderBot D] (f : D →𝒄 D) :
    fix (alternating f) = fun _ => fix f :=
  Proofs.CounterSemiringIndependence.standard_cycle f

end Silmaril.Calco2019.PointedCpo
