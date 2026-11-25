module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Probability in CALCO 2019 Examples 10(3) and 20(3) -/

@[expose] public section

open scoped ENNReal BigOperators Classical

namespace Silmaril.Calco2019.Examples.Probability


variable {X : Type*} {Y : Type*} {Z : Type*}

/-- Every state has a direct return of positive probability. -/
def Guarded (f : X → PMF (Y ⊕ Z)) : Prop :=
  ∀ x, ∃ y, 0 < f x (.inl y)


noncomputable def step (f : X → PMF (Y ⊕ X)) (g : X → Y → ℝ≥0∞) (x : X) (y : Y) :
    ℝ≥0∞ :=
  f x (.inl y) + ∑' z, f x (.inr z) * g z y

/-- Truncate the run after at most this many steps, discarding all unfinished runs. -/
noncomputable def approx (f : X → PMF (Y ⊕ X)) : ℕ → X → Y → ℝ≥0∞
  | 0 => fun _ _ => 0
  | n + 1 => step f (approx f n)

/-- The unnormalized probability of a finite successful run. -/
noncomputable def least (f : X → PMF (Y ⊕ X)) (x : X) (y : Y) : ℝ≥0∞ :=
  ⨆ n, approx f n x y

noncomputable def mass (g : X → Y → ℝ≥0∞) (x : X) : ℝ≥0∞ := ∑' y, g x y

/-- Example 20(3)'s pointwise normalization of the eventual return weights. -/
noncomputable def normalizedWeight (f : X → PMF (Y ⊕ X)) (x : X) (y : Y) : ℝ≥0∞ :=
  least f x y / mass (least f) x

/-- The paper’s unscaled survival weight at state `n`, namely `1/2 + 2⁻ⁿ`. -/
noncomputable def survivalWeight (n : ℕ) : ℝ≥0∞ := 2⁻¹ + (2⁻¹ : ℝ≥0∞) ^ n

/-- The paper's direct exit probability, written as `2⁻⁽ⁿ⁺¹⁾ / (1/2 + 2⁻ⁿ)`. -/
noncomputable def exit (n : ℕ) : ℝ≥0∞ :=
  (2⁻¹ : ℝ≥0∞) ^ (n + 1) / survivalWeight n

noncomputable def advance (n : ℕ) : ℝ≥0∞ := survivalWeight (n + 1) / survivalWeight n

theorem survivalWeight_ne_zero (n : ℕ) : survivalWeight n ≠ 0 := by
  simp [survivalWeight]

theorem survivalWeight_ne_top (n : ℕ) : survivalWeight n ≠ ∞ := by
  simp [survivalWeight]

theorem exit_add_advance (n : ℕ) : exit n + advance n = 1 := by
  rw [exit, advance, ← ENNReal.add_div]
  have h : (2⁻¹ : ℝ≥0∞) ^ (n + 1) + survivalWeight (n + 1) = survivalWeight n := by
    rw [survivalWeight, survivalWeight, pow_succ, add_left_comm, ← mul_add,
      ENNReal.inv_two_add_inv_two, mul_one]
  rw [h, ENNReal.div_self (survivalWeight_ne_zero n) (survivalWeight_ne_top n)]

/-- A distribution supported on one exit and one continuation. -/
noncomputable def twoPoint (y : Y) (z : Z) (p q : ℝ≥0∞) (h : p + q = 1) : PMF (Y ⊕ Z) := by
  classical
  exact PMF.ofFinset
    (fun w => if w = .inl y then p else if w = .inr z then q else 0)
    {.inl y, .inr z}
    (by simpa using h)
    (by intro w hw; simp_all)

@[simp] theorem twoPoint_inl (y : Y) (z : Z) (p q : ℝ≥0∞) (h : p + q = 1) (y' : Y) :
    twoPoint y z p q h (.inl y') = if y' = y then p else 0 := by
  classical
  simp [twoPoint, PMF.ofFinset_apply]

@[simp] theorem twoPoint_inr (y : Y) (z : Z) (p q : ℝ≥0∞) (h : p + q = 1) (z' : Z) :
    twoPoint y z p q h (.inr z') = if z' = z then q else 0 := by
  classical
  simp [twoPoint, PMF.ofFinset_apply]

/-- Reindex the paper’s chain beginning at the indicated absolute state. -/
noncomputable def chainFrom (offset : ℕ) (label : ℕ → Y) (n : ℕ) : PMF (Y ⊕ ℕ) :=
  twoPoint (label n) (n + 1) (exit (n + offset)) (advance (n + offset))
    (exit_add_advance (n + offset))

/-- The printed singleton-result loop uses a constant label. -/
noncomputable def chain (label : ℕ → Y) (n : ℕ) : PMF (Y ⊕ ℕ) :=
  chainFrom 0 label n

@[simp] theorem chain_inl (label : ℕ → Y) (n : ℕ) (y : Y) :
    chain label n (.inl y) = if y = label n then exit n else 0 := by
  simp [chain, chainFrom]

@[simp] theorem chain_inr (label : ℕ → Y) (n k : ℕ) :
    chain label n (.inr k) = if k = n + 1 then advance n else 0 := by
  by_cases hk : k = n + 1 <;> simp [chain, chainFrom, hk]

/-- The first exit is labeled false. All subsequent exits are labeled true. -/
def coloredExit (n : ℕ) : Bool := n != 0

/-- The fragment of guarded iteration needed to test the probability example.
Fixpoints are required to respect pure maps of results and pure changes of state. -/
structure NatIteration where
  run (f : ℕ → PMF (ℕ ⊕ ℕ)) : Guarded f → ℕ → PMF ℕ
  fixpoint (f : ℕ → PMF (ℕ ⊕ ℕ)) (hf : Guarded f) :
    step f (fun x y => run f hf x y) = fun x y => run f hf x y
  naturality (f g : ℕ → PMF (ℕ ⊕ ℕ)) (hf : Guarded f) (hg : Guarded g) (h : ℕ → ℕ) :
    (∀ n, (f n).map (Sum.map h id) = g n) →
      ∀ n, (run f hf n).map h = run g hg n
  uniformity (f g : ℕ → PMF (ℕ ⊕ ℕ)) (hf : Guarded f) (hg : Guarded g) (h : ℕ → ℕ) :
    (∀ n, (f n).map (Sum.map id h) = g (h n)) →
      ∀ n, run f hf n = run g hg (h n)

end Silmaril.Calco2019.Examples.Probability
