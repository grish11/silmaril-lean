module

public import Silmaril.Data.TimeSeries.Operations.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Data.Option.NAry

import Silmaril.Proofs.Data.TimeSeries.Operations.Laws

/-!
# Laws for finite signal operations

With times and weights held fixed, additive perturbations propagate through sampling,
differences, valid slopes, interpolation and weighted means by the same operators.
For an EMA run with a fixed initial state, the perturbation has a zero initial state.
The weighted mean also has a deterministic error bound for nonnegative weights.
-/

public section

namespace Silmaril.Data.TimeSeries.Operations

open scoped BigOperators

variable {n : ℕ} {A : Type*}

/-- Each adjacent step of a uniform grid is the supplied signed step. -/
@[simp] theorem uniformTimes_diff (start step : ℝ) (i : Fin (n - 1)) :
    forwardDiff (uniformTimes start step n) i = step :=
  Proofs.Data.TimeSeries.Operations.uniformTimes_diff start step i

/-- An additive perturbation of the continuous-time signal is sampled at the same times. -/
theorem sampleAt_add [Add A] (times : Fin n → ℝ) (f e : ℝ → A) :
    sampleAt times (f + e) = sampleAt times f + sampleAt times e := rfl

section Module

variable [AddCommGroup A]

/-- The forward difference of a constant signal vanishes. -/
@[simp] theorem forwardDiff_const (a : A) (i : Fin (n - 1)) :
    forwardDiff (fun _ => a) i = 0 := by simp [forwardDiff]

/-- An additive perturbation contributes its own forward differences. -/
theorem forwardDiff_add (x e : Fin n → A) (i : Fin (n - 1)) :
    forwardDiff (x + e) i = forwardDiff x i + forwardDiff e i := by
  simp only [forwardDiff, Pi.add_apply, add_sub_add_comm]

variable [Module ℝ A]

/-- An adjacent pair has no slope exactly when its two timestamps coincide. -/
theorem forwardSlope?_eq_none_iff (times : Fin n → ℝ) (x : Fin n → A)
    (i : Fin (n - 1)) : forwardSlope? times x i = none ↔
      times (segmentRight i) = times (segmentLeft i) := by
  rw [← (sub_eq_zero : forwardDiff times i = 0 ↔ _)]
  change _ ↔ forwardDiff times i = 0
  by_cases h : forwardDiff times i = 0 <;> simp [forwardSlope?, h]

/-- On a uniform grid with nonzero step, slopes are forward differences scaled by its inverse. -/
theorem forwardSlope?_uniform (start step : ℝ) (h : step ≠ 0) (x : Fin n → A)
    (i : Fin (n - 1)) :
    forwardSlope? (uniformTimes start step n) x i = some (step⁻¹ • forwardDiff x i) := by
  simp [forwardSlope?, h]

/-- A valid slope of a perturbed signal sums the signal and perturbation slopes.
Both sides are `none` at an equal-time pair. -/
theorem forwardSlope?_add (times : Fin n → ℝ) (x e : Fin n → A) (i : Fin (n - 1)) :
    forwardSlope? times (x + e) i =
      Option.map₂ (· + ·) (forwardSlope? times x i) (forwardSlope? times e i) :=
  Proofs.Data.TimeSeries.Operations.forwardSlope?_add times x e i

@[simp] theorem linearInterpolate_left (t₀ t₁ : ℝ) (x₀ x₁ : A) :
    linearInterpolate t₀ t₁ x₀ x₁ t₀ = x₀ := by simp [linearInterpolate]

/-- The right endpoint is recovered when the timestamps differ. -/
theorem linearInterpolate_right (t₀ t₁ : ℝ) (x₀ x₁ : A) (h : t₁ ≠ t₀) :
    linearInterpolate t₀ t₁ x₀ x₁ t₁ = x₁ :=
  Proofs.Data.TimeSeries.Operations.linearInterpolate_right t₀ t₁ x₀ x₁ h

/-- At coincident times the left value is used, independently of the query. -/
@[simp] theorem linearInterpolate_sameTime (t : ℝ) (x₀ x₁ : A) (query : ℝ) :
    linearInterpolate t t x₀ x₁ query = x₀ := by simp [linearInterpolate]

/-- With fixed times, interpolate an additive perturbation using the same two coefficients. -/
theorem linearInterpolate_add (t₀ t₁ t : ℝ) (x₀ x₁ e₀ e₁ : A) :
    linearInterpolate t₀ t₁ (x₀ + e₀) (x₁ + e₁) t =
      linearInterpolate t₀ t₁ x₀ x₁ t + linearInterpolate t₀ t₁ e₀ e₁ t :=
  Proofs.Data.TimeSeries.Operations.linearInterpolate_add t₀ t₁ t x₀ x₁ e₀ e₁

/-- Grid lookup recovers each sample when timestamps are distinct. -/
theorem interpolateGrid?_sample (times : Fin n → ℝ) (x : Fin n → A)
    (ht : Function.Injective times) (i : Fin n) :
    interpolateGrid? times x (times i) = some (x i) :=
  Proofs.Data.TimeSeries.Operations.interpolateGrid?_sample times x ht i

/-- Grid lookup has no result exactly when there is neither a matching timestamp
nor a bracketing adjacent pair. -/
theorem interpolateGrid?_eq_none_iff (times : Fin n → ℝ) (x : Fin n → A) (t : ℝ) :
    interpolateGrid? times x t = none ↔
      (∀ j, times j ≠ t) ∧
      ∀ i, ¬ (times (segmentLeft i) ≤ t ∧ t ≤ times (segmentRight i)) :=
  Proofs.Data.TimeSeries.Operations.interpolateGrid?_eq_none_iff times x t

/-- A perturbed weighted mean is the sum of the weighted signal and perturbation means. -/
theorem weightedMean_add (w : Fin n → ℝ) (x e : Fin n → A) :
    weightedMean w (x + e) = weightedMean w x + weightedMean w e :=
  Proofs.Data.TimeSeries.Operations.weightedMean_add w x e

/-- Normalization preserves constant signals whenever the total weight is nonzero. -/
theorem weightedMean_const (w : Fin n → ℝ) (a : A) (hw : (∑ i, w i) ≠ 0) :
    weightedMean w (fun _ => a) = a :=
  Proofs.Data.TimeSeries.Operations.weightedMean_const w a hw

/-- The first EMA output blends the seed with the first sample. -/
theorem ema_first (alpha : ℝ) (seed : A) (x : Fin (n + 1) → A) :
    ema alpha seed x 0 = (1 - alpha) • seed + alpha • x 0 := rfl

/-- Every subsequent EMA output blends the previous output with the current sample. -/
theorem ema_succ (alpha : ℝ) (seed : A) (x : Fin (n + 1) → A) (i : Fin n) :
    ema alpha seed x i.succ =
      (1 - alpha) • ema alpha seed x i.castSucc + alpha • x i.succ := rfl

@[simp] theorem ema_zero_alpha (seed : A) (x : Fin n → A) (i : Fin n) :
    ema 0 seed x i = seed :=
  Proofs.Data.TimeSeries.Operations.ema_zero_alpha seed x i

@[simp] theorem ema_one_alpha (seed : A) (x : Fin n → A) (i : Fin n) :
    ema 1 seed x i = x i :=
  Proofs.Data.TimeSeries.Operations.ema_one_alpha seed x i

/-- Seeding the EMA with the constant sample value preserves it at every index. -/
theorem ema_const (alpha : ℝ) (a : A) (i : Fin n) :
    ema alpha a (fun _ => a) i = a :=
  Proofs.Data.TimeSeries.Operations.ema_const alpha a i

/-- EMA is additive jointly in its initial state and samples. -/
theorem ema_add (alpha : ℝ) (seed noiseSeed : A) (x e : Fin n → A) (i : Fin n) :
    ema alpha (seed + noiseSeed) (x + e) i =
      ema alpha seed x i + ema alpha noiseSeed e i :=
  Proofs.Data.TimeSeries.Operations.ema_add alpha seed noiseSeed x e i

/-- For a fixed initial state, the added perturbation EMA uses a zero seed. -/
theorem ema_add_noise (alpha : ℝ) (seed : A) (x e : Fin n → A) (i : Fin n) :
    ema alpha seed (x + e) i = ema alpha seed x i + ema alpha 0 e i := by
  simpa only [add_zero] using ema_add alpha seed 0 x e i

end Module

variable [SeminormedAddCommGroup A] [NormedSpace ℝ A]

/-- With nonnegative weights of positive total, the weighted mean preserves
any common bound on the sample norms. -/
theorem norm_weightedMean_le (w : Fin n → ℝ) (x : Fin n → A) (ε : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpos : 0 < ∑ i, w i) (hx : ∀ i, ‖x i‖ ≤ ε) :
    ‖weightedMean w x‖ ≤ ε :=
  Proofs.Data.TimeSeries.Operations.norm_weightedMean_le w x ε hw hpos hx

/-- Under nonnegative weights of positive total, the weighted mean cannot amplify
a uniform bound on additive sample noise. -/
theorem norm_weightedMean_residual_le (w : Fin n → ℝ) (x e : Fin n → A) (ε : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpos : 0 < ∑ i, w i) (he : ∀ i, ‖e i‖ ≤ ε) :
    ‖weightedMean w (x + e) - weightedMean w x‖ ≤ ε := by
  rw [weightedMean_add, add_sub_cancel_left]
  exact norm_weightedMean_le w e ε hw hpos he

end Silmaril.Data.TimeSeries.Operations
