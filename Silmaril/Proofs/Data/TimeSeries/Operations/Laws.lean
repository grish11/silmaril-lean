module

public import Silmaril.Data.TimeSeries.Operations.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Data.Option.NAry

import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

public section

namespace Silmaril.Proofs.Data.TimeSeries.Operations

open Silmaril.Data.TimeSeries.Operations
open scoped BigOperators

variable {n : ℕ} {A : Type*}

theorem uniformTimes_diff (start step : ℝ) (i : Fin (n - 1)) :
    forwardDiff (uniformTimes start step n) i = step := by
  simp [forwardDiff, uniformTimes, segmentRight, segmentLeft, Nat.cast_add, add_mul]

section Module

variable [AddCommGroup A] [Module ℝ A]

theorem forwardSlope?_add (times : Fin n → ℝ) (x e : Fin n → A) (i : Fin (n - 1)) :
    forwardSlope? times (x + e) i =
      Option.map₂ (· + ·) (forwardSlope? times x i) (forwardSlope? times e i) := by
  by_cases h : forwardDiff times i = 0
  · simp [forwardSlope?, h]
  · simp only [forwardSlope?, h, ite_false, Option.map₂_some_some]
    simp only [forwardDiff, Pi.add_apply, add_sub_add_comm, smul_add]

theorem linearInterpolate_right (t₀ t₁ : ℝ) (x₀ x₁ : A) (h : t₁ ≠ t₀) :
    linearInterpolate t₀ t₁ x₀ x₁ t₁ = x₁ := by
  have hstep : t₁ - t₀ ≠ 0 := sub_ne_zero.mpr h
  simp [linearInterpolate, div_self hstep]

theorem linearInterpolate_add (t₀ t₁ t : ℝ) (x₀ x₁ e₀ e₁ : A) :
    linearInterpolate t₀ t₁ (x₀ + e₀) (x₁ + e₁) t =
      linearInterpolate t₀ t₁ x₀ x₁ t + linearInterpolate t₀ t₁ e₀ e₁ t := by
  simp only [linearInterpolate, smul_add, add_add_add_comm]

theorem interpolateGrid?_sample (times : Fin n → ℝ) (x : Fin n → A)
    (ht : Function.Injective times) (i : Fin n) :
    interpolateGrid? times x (times i) = some (x i) := by
  unfold interpolateGrid?
  split
  · rename_i j hj
    have hmatch : times j = times i := of_decide_eq_true (List.find?_some (p := fun k => decide (times k = times i)) hj)
    rw [ht hmatch]
  · rename_i hnone
    have hmiss := List.find?_eq_none.mp hnone i (List.mem_finRange i)
    exact (hmiss (decide_eq_true rfl)).elim

theorem interpolateGrid?_eq_none_iff (times : Fin n → ℝ) (x : Fin n → A) (t : ℝ) :
    interpolateGrid? times x t = none ↔
      (∀ j, times j ≠ t) ∧
      ∀ i, ¬ (times (segmentLeft i) ≤ t ∧ t ≤ times (segmentRight i)) := by
  unfold interpolateGrid?
  split
  · rename_i j hj
    have hmatch : times j = t := of_decide_eq_true (List.find?_some (p := fun k => decide (times k = t)) hj)
    simp [show ¬ (∀ k, times k ≠ t) from fun h => h j hmatch]
  · rename_i hnone
    have hmiss : ∀ j, times j ≠ t := by
      simpa [List.find?_eq_none, List.mem_finRange] using hnone
    simp [hmiss, List.findSome?_eq_none_iff, List.mem_finRange, interpolateSegment?]

theorem weightedMean_add (w : Fin n → ℝ) (x e : Fin n → A) :
    weightedMean w (x + e) = weightedMean w x + weightedMean w e := by
  simp only [weightedMean, Pi.add_apply, smul_add, Finset.sum_add_distrib]

theorem weightedMean_const (w : Fin n → ℝ) (a : A) (hw : (∑ i, w i) ≠ 0) :
    weightedMean w (fun _ => a) = a := by
  rw [weightedMean, ← Finset.sum_smul, smul_smul, inv_mul_cancel₀ hw, one_smul]

theorem ema_add (alpha : ℝ) (seed noiseSeed : A) (x e : Fin n → A) (i : Fin n) :
    ema alpha (seed + noiseSeed) (x + e) i =
      ema alpha seed x i + ema alpha noiseSeed e i := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    induction i using Fin.induction with
    | zero => simp only [ema, Fin.induction_zero, Pi.add_apply, smul_add, add_add_add_comm]
    | succ i ih =>
      simp only [ema, Fin.induction_succ, Pi.add_apply] at ih ⊢
      rw [ih]
      simp only [smul_add, add_add_add_comm]

theorem ema_const (alpha : ℝ) (a : A) (i : Fin n) :
    ema alpha a (fun _ => a) i = a := by
  have h : (1 - alpha) • a + alpha • a = a := by
    rw [← add_smul, sub_add_cancel, one_smul]
  cases n with
  | zero => exact i.elim0
  | succ n =>
    induction i using Fin.induction with
    | zero => simpa only [ema, Fin.induction_zero] using h
    | succ i ih =>
      simp only [ema, Fin.induction_succ] at ih ⊢
      rw [ih, h]

theorem ema_zero_alpha (seed : A) (x : Fin n → A) (i : Fin n) :
    ema 0 seed x i = seed := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    induction i using Fin.induction with
    | zero => simp [ema]
    | succ i ih => simpa [ema] using ih

theorem ema_one_alpha (seed : A) (x : Fin n → A) (i : Fin n) :
    ema 1 seed x i = x i := by
  cases n with
  | zero => exact i.elim0
  | succ n => exact Fin.cases (by simp [ema]) (fun j => by simp [ema]) i

end Module

variable [SeminormedAddCommGroup A] [NormedSpace ℝ A]

theorem norm_weightedMean_le (w : Fin n → ℝ) (x : Fin n → A) (ε : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpos : 0 < ∑ i, w i) (hx : ∀ i, ‖x i‖ ≤ ε) :
    ‖weightedMean w x‖ ≤ ε := by
  have hsum : ‖∑ i, w i • x i‖ ≤ (∑ i, w i) * ε := by
    calc
      ‖∑ i, w i • x i‖ ≤ ∑ i, ‖w i • x i‖ := norm_sum_le _ _
      _ ≤ ∑ i, w i * ε := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i)]
        exact mul_le_mul_of_nonneg_left (hx i) (hw i)
      _ = (∑ i, w i) * ε := (Finset.sum_mul _ _ _).symm
  rw [weightedMean, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hpos.le)]
  calc
    (∑ i, w i)⁻¹ * ‖∑ i, w i • x i‖ ≤ (∑ i, w i)⁻¹ * ((∑ i, w i) * ε) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hpos.le)
    _ = ε := by rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]

end Silmaril.Proofs.Data.TimeSeries.Operations
