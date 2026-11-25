module

public import Silmaril.Semantics.Calco2019.Examples.Probability.Defs
import Silmaril.Proofs.Semantics.Calco2019.Examples.Probability
import Silmaril.Proofs.Semantics.Calco2019.Examples.ProbabilityArithmetic

/-! # Probabilistic guarded loops, their least solutions, and normalization -/

public section

open scoped ENNReal BigOperators Classical

namespace Silmaril.Calco2019.Examples.Probability


variable {X : Type*} {Y : Type*}

/-- Nonnegative summation commutes with the supremum of an increasing sequence. -/
theorem tsum_iSup_nat {A : Type*} (g : ℕ → A → ℝ≥0∞) (hg : Monotone g) :
    (∑' a, ⨆ n, g n a) = ⨆ n, ∑' a, g n a :=
  Proofs.tsum_iSup_nat g hg

/-- The supremum of the finite approximants is a fixpoint of the unnormalized unfolding. -/
theorem least_fixpoint (f : X → PMF (Y ⊕ X)) : step f (least f) = least f :=
  Proofs.least_fixpoint f

/-- The finite-run weights lie below every prefixed point of the same unfolding. -/
theorem least_le (f : X → PMF (Y ⊕ X)) {g : X → Y → ℝ≥0∞}
    (hg : step f g ≤ g) : least f ≤ g :=
  Proofs.least_le f hg

theorem mass_le_one (f : X → PMF (Y ⊕ X)) (x : X) : mass (least f) x ≤ 1 :=
  Proofs.mass_le_one f x

theorem mass_pos (f : X → PMF (Y ⊕ X)) (hf : Guarded f) (x : X) : 0 < mass (least f) x :=
  Proofs.mass_pos f hf x

/-- The printed normalization is well-defined for guarded loops. -/
noncomputable def normalized (f : X → PMF (Y ⊕ X)) (hf : Guarded f) (x : X) : PMF Y :=
  PMF.normalize (least f x) (by exact (mass_pos f hf x).ne')
    (by exact ne_top_of_le_ne_top ENNReal.one_ne_top (mass_le_one f x))

@[simp] theorem normalized_apply (f : X → PMF (Y ⊕ X)) (hf : Guarded f) (x : X) (y : Y) :
    normalized f hf x y = normalizedWeight f x y := by
  rw [normalizedWeight, div_eq_mul_inv]
  exact PMF.normalize_apply _ _ _

/-- Completing the least subdistribution with an explicit fallback gives a PMF fixpoint.
The fallback receives exactly the probability of divergence. -/
theorem completion (f : X → PMF (Y ⊕ X)) (fallback : PMF Y) :
    let g := fun x y => least f x y + (1 - mass (least f) x) * fallback y
    (∀ x, mass g x = 1) ∧ step f g = g :=
  Proofs.completion f fallback

theorem chain_guarded (label : ℕ → Y) : Guarded (chain label) :=
  Proofs.chain_guarded label

/-- The exit weight is the rational expression printed in Example 20(3). -/
theorem exit_printed (n : ℕ) : exit n = 1 / ((2 : ℝ≥0∞) ^ n + 2) :=
  ArithmeticProofs.exit_printed n

/-- The probability of first exiting at state `n` is the product of the preceding
continuation weights and the exit weight at `n`. -/
theorem first_exit_probability (n : ℕ) :
    (∏ i ∈ Finset.range n, advance i) * exit n = 1 / (3 * (2 : ℝ≥0∞) ^ n) :=
  ArithmeticProofs.first_exit_probability n

/-- With any exit labeling, the probability of the printed loop eventually returning
from state zero is two thirds. -/
theorem chain_mass_zero (label : ℕ → Y) : mass (least (chain label)) 0 = 2 / 3 :=
  Proofs.chain_mass_zero label

/-- The probabilities of individual finite returns are given by a geometric series
filtered by the exit labels. -/
theorem scaled_least (label : ℕ → Y) (n : ℕ) (y : Y) :
    survivalWeight n * least (chain label) n y =
      ∑' i : ℕ, if y = label (n + i) then (2⁻¹ : ℝ≥0∞) ^ (n + i + 1) else 0 :=
  Proofs.scaled_least label n y

theorem normalized_first_exit : normalizedWeight (chain coloredExit) 0 false = 1 / 2 :=
  Proofs.normalized_first_exit

theorem unfolded_first_exit :
    step (chain coloredExit) (normalizedWeight (chain coloredExit)) 0 false = 1 / 3 :=
  Proofs.unfolded_first_exit

/-- On a guarded loop with the printed transition probabilities, normalization fails
the fixpoint equation at its initial state and first result label. -/
theorem normalized_not_fixpoint :
    step (chain coloredExit) (normalizedWeight (chain coloredExit)) 0 false ≠
      normalizedWeight (chain coloredExit) 0 false :=
  Proofs.normalized_not_fixpoint

/-- Fixpoints for the printed guard cannot satisfy both pure naturality and pure
uniformity, even with states and results restricted to natural numbers. -/
theorem no_nat_iteration : IsEmpty NatIteration :=
  Proofs.no_nat_iteration

end Silmaril.Calco2019.Examples.Probability
