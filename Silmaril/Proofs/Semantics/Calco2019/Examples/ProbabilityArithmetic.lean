module

public import Silmaril.Semantics.Calco2019.Examples.Probability.Defs
import Mathlib.Tactic.NormNum

public section

open scoped ENNReal BigOperators

namespace Silmaril.Calco2019.Examples.Probability.ArithmeticProofs

private theorem pow_inv_two_cancel (n : ℕ) : (2 : ℝ≥0∞) ^ n * (2⁻¹ : ℝ≥0∞) ^ n = 1 := by
  rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by simp), one_pow]

theorem exit_printed (n : ℕ) : exit n = 1 / ((2 : ℝ≥0∞) ^ n + 2) := by
  apply (ENNReal.eq_div_iff (by simp) (by simp)).2
  apply (ENNReal.mul_right_inj (survivalWeight_ne_zero n) (survivalWeight_ne_top n)).mp
  calc
    survivalWeight n * (((2 : ℝ≥0∞) ^ n + 2) * exit n) =
        ((2 : ℝ≥0∞) ^ n + 2) * (survivalWeight n * exit n) := by ac_rfl
    _ = ((2 : ℝ≥0∞) ^ n + 2) * (2⁻¹ : ℝ≥0∞) ^ (n + 1) := by
      rw [exit, ENNReal.mul_div_cancel (survivalWeight_ne_zero n) (survivalWeight_ne_top n)]
    _ = survivalWeight n * 1 := by
      rw [mul_one, add_mul, survivalWeight]
      congr 1
      · rw [pow_succ, ← mul_assoc, pow_inv_two_cancel, one_mul]
      · rw [pow_succ', ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by simp), one_mul]

private theorem survive (n : ℕ) : survivalWeight 0 * (∏ i ∈ Finset.range n, advance i) = survivalWeight n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ih, advance,
      ENNReal.mul_div_cancel (survivalWeight_ne_zero n) (survivalWeight_ne_top n)]

theorem first_exit_probability (n : ℕ) :
    (∏ i ∈ Finset.range n, advance i) * exit n = 1 / (3 * (2 : ℝ≥0∞) ^ n) := by
  have hzero : (2 : ℝ≥0∞) * survivalWeight 0 = 3 := by
    rw [survivalWeight, pow_zero, mul_add, mul_one, ENNReal.mul_inv_cancel (by norm_num) (by simp)]
    norm_num
  apply (ENNReal.eq_div_iff (by simp) (ENNReal.mul_ne_top (by simp) (by simp))).2
  calc
    (3 * (2 : ℝ≥0∞) ^ n) * ((∏ i ∈ Finset.range n, advance i) * exit n) =
        (2 * (2 : ℝ≥0∞) ^ n) * ((survivalWeight 0 * ∏ i ∈ Finset.range n, advance i) * exit n) := by
      rw [← hzero]
      ac_rfl
    _ = (2 * (2 : ℝ≥0∞) ^ n) * (2⁻¹ : ℝ≥0∞) ^ (n + 1) := by
      rw [survive, exit, ENNReal.mul_div_cancel (survivalWeight_ne_zero n) (survivalWeight_ne_top n)]
    _ = (2 * (2⁻¹ : ℝ≥0∞)) * ((2 : ℝ≥0∞) ^ n * (2⁻¹ : ℝ≥0∞) ^ n) := by
      rw [pow_succ']
      ac_rfl
    _ = 1 := by
      rw [pow_inv_two_cancel, mul_one, ENNReal.mul_inv_cancel (by norm_num) (by simp)]

end Silmaril.Calco2019.Examples.Probability.ArithmeticProofs
