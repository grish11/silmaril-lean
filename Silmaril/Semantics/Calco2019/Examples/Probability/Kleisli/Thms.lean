module

public import Silmaril.Semantics.Calco2019.Examples.Probability.Thms
public import Silmaril.Semantics.Calco2019.CompleteElgot.Defs
import Silmaril.Proofs.Semantics.Calco2019.Examples.ProbabilityKleisli

/-! # The CALCO guard and no-iteration result for Mathlib's PMF monad -/

public section

open scoped ENNReal

namespace Silmaril.Calco2019.Examples.Probability

universe u

open CategoryTheory

/-- Example 10(3)'s guard satisfies the three axioms of CALCO Definition 6. -/
noncomputable def pmfGuard : MonadGuardedness typeCoproducts.{u} (ofTypeMonad PMF) :=
  KleisliProofs.pmfGuard

theorem pmf_guarded_iff {A B C : Type u} (f : A → PMF (B ⊕ C)) :
    pmfGuard.guarded (computation PMF f) ↔ Guarded f :=
  KleisliProofs.guarded_iff f

/-- The weight unfolding is the Kleisli fixpoint equation for Mathlib's PMF monad. -/
theorem pmf_fixpoint_iff {A B : Type u} (f : A → PMF (B ⊕ A)) (g : A → PMF B) :
    Guardedness.IsFixpoint (P := typeCoproducts.kleisli (ofTypeMonad PMF))
        (computation PMF f) (computation PMF g) ↔
      step f (fun x y => g x y) = fun x y => g x y :=
  KleisliProofs.pmf_fixpoint_iff f g

/-- Normalizing the concrete two-label loop fails the categorical fixpoint equation. -/
theorem normalized_pmf_counterexample :
    ¬ Guardedness.IsFixpoint (P := typeCoproducts.kleisli (ofTypeMonad PMF))
      (computation PMF (chain coloredExit))
      (computation PMF (normalized (chain coloredExit) (chain_guarded coloredExit))) :=
  KleisliProofs.normalized_pmf_counterexample

/-- Normalization gives a PMF fixpoint if the least solution has unit mass at every state. -/
theorem normalized_pmf_fixpoint_of_mass_one {A B : Type u} (f : A → PMF (B ⊕ A))
    (hf : Guarded f) (hm : ∀ x, mass (least f) x = 1) :
    Guardedness.IsFixpoint (P := typeCoproducts.kleisli (ofTypeMonad PMF))
      (computation PMF f) (computation PMF (normalized f hf)) :=
  KleisliProofs.normalized_pmf_fixpoint_of_mass_one f hf hm

/-- The proposed probability model with this guard cannot satisfy CALCO Definition 19(2). -/
theorem no_conway_uniform (I : pmfGuard.{0}.Conway)
    (hu : I.toFixpoints.Uniform (Kleisli.Adjunction.toKleisli (ofTypeMonad PMF))) : False :=
  KleisliProofs.no_conway_uniform I hu

/-- The pure loop with no result type would require a PMF on the empty type. -/
theorem no_total_fixpoints (F : (Guardedness.greatest (typeCoproducts.kleisli
    (ofTypeMonad PMF.{0}))).Fixpoints) : False :=
  KleisliProofs.no_total_fixpoints F

end Silmaril.Calco2019.Examples.Probability
