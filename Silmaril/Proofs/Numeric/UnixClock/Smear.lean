module

public import Silmaril.Numeric.UnixClock.Defs
import Silmaril.Proofs.Numeric.UnixClock.Convention
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Order.IntermediateValue

public section

namespace Silmaril.Proofs.Numeric.UnixClock

open Silmaril.Numeric.UnixClock Set
open scoped ENNReal

private theorem abs_leap (sign : Leap) : |(sign.seconds : ℝ)| = 1 := by
  cases sign <;> norm_num [Leap.seconds]

private theorem abs_step_sub_ramp {edge : ℝ} (ramp : Ramp edge) (t : ℝ) :
    |Schedule.step edge t - ramp.value t| ≤ 1 := by
  obtain ⟨hl, hr⟩ := ramp.range_value t
  unfold Schedule.step
  split <;> apply abs_le.mpr <;> constructor <;> linarith

theorem step_eq_ramp_off_window {edge : ℝ} (ramp : Ramp edge) {t : ℝ}
    (ht : t ∉ ramp.window) : Schedule.step edge t = ramp.value t := by
  by_cases hl : ramp.left ≤ t
  · have hr : ramp.right ≤ t := le_of_not_gt fun h => ht ⟨hl, h⟩
    simp [Schedule.step, ramp.edge_le_right.trans hr, ramp.after t hr]
  · have hlt := lt_of_not_ge hl
    simp [Schedule.step, (hlt.trans_le ramp.left_le_edge).not_ge, ramp.before t hlt.le]

variable (s : Schedule) (ramps : s.Ramps)

theorem smear_sub_sharp (t : ℝ) :
    s.smear ramps t - s.sharp t =
      ∑ d ∈ s.active ramps t, ((s.leap d).seconds : ℝ) *
        (Schedule.step (s.midnight d) t - (ramps d).value t) := by
  unfold Schedule.smear Schedule.sharp Schedule.correction Schedule.active
  rw [sub_sub_sub_cancel_left, ← Finset.sum_sub_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  rw [← mul_sub]
  split_ifs with h
  · rfl
  · rw [step_eq_ramp_off_window (ramps d) h, sub_self, mul_zero]

theorem smear_error_le_active (t : ℝ) :
    |s.smear ramps t - s.sharp t| ≤ (s.active ramps t).card := by
  rw [smear_sub_sharp]
  calc
    _ ≤ ∑ d ∈ s.active ramps t, |((s.leap d).seconds : ℝ) *
        (Schedule.step (s.midnight d) t - (ramps d).value t)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ s.active ramps t, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      rw [abs_mul, abs_leap, one_mul]
      exact abs_step_sub_ramp (ramps d) t
    _ = _ := by simp

theorem smear_eq_sharp_off_windows {t : ℝ}
    (h : ∀ d ∈ s.transitions, t ∉ (ramps d).window) : s.smear ramps t = s.sharp t := by
  have he : s.active ramps t = ∅ := by
    exact Finset.filter_eq_empty_iff.mpr fun _ hd => h _ hd
  exact sub_eq_zero.mp (by simp [smear_sub_sharp, he])

theorem smear_worstError_le {smearDomain sharpDomain : Set ℝ} {k : Nat}
    (h : ∀ t ∈ smearDomain ∩ sharpDomain, (s.active ramps t).card ≤ k) :
    (s.smearOn ramps smearDomain).worstError (s.sharpOn sharpDomain) ≤ k := by
  apply (worstError_le_iff _ _ _).mpr
  intro t hs hh
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal ((smear_error_le_active s ramps t).trans
    (Nat.cast_le.mpr (h t ⟨hs, hh⟩)))

theorem smear_worstError_le_one {smearDomain sharpDomain : Set ℝ}
    (h : ∀ d ∈ s.transitions, ∀ e ∈ s.transitions, d ≠ e →
      Disjoint (ramps d).window (ramps e).window) :
    (s.smearOn ramps smearDomain).worstError (s.sharpOn sharpDomain) ≤ 1 := by
  simpa using (smear_worstError_le s ramps (k := 1) fun t _ =>
    Finset.card_le_one.mpr fun d hd e he => by
      have hd' := Finset.mem_filter.mp hd
      have he' := Finset.mem_filter.mp he
      by_contra hdne
      exact Set.disjoint_left.mp (h d hd'.1 e he'.1 hdne) hd'.2 he'.2)

theorem smear_error_at_left_edge {d : Int} (h : s.active ramps (s.midnight d) = {d})
    (hleft : (ramps d).left = s.midnight d) :
    |s.smear ramps (s.midnight d) - s.sharp (s.midnight d)| = 1 := by
  rw [smear_sub_sharp, h, Finset.sum_singleton, (ramps d).before _ hleft.ge]
  simp [Schedule.step, abs_leap]

theorem smear_continuous : Continuous (s.smear ramps) := by
  apply (continuous_id.sub continuous_const).sub
  exact continuous_finsetSum _ fun d _ => continuous_const.mul (ramps d).continuous_value

private theorem correction_bound (t : ℝ) : |s.correction ramps t| ≤ s.transitions.card := by
  unfold Schedule.correction
  calc
    _ ≤ ∑ d ∈ s.transitions, |((s.leap d).seconds : ℝ) * (ramps d).value t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ s.transitions, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      obtain ⟨hl, hr⟩ := (ramps d).range_value t
      simpa [abs_mul, abs_leap, abs_of_nonneg hl] using hr
    _ = _ := by simp

theorem smear_surjective : Function.Surjective (s.smear ramps) := by
  intro y
  let a := y + (s.baseline : ℝ) - s.transitions.card
  let b := y + (s.baseline : ℝ) + s.transitions.card
  have hab : a ≤ b := by
    dsimp [a, b]
    linarith [Nat.cast_nonneg (α := ℝ) s.transitions.card]
  have ha : s.smear ramps a ≤ y := by
    have := (abs_le.mp (correction_bound s ramps a)).1
    dsimp [Schedule.smear, a] at *
    linarith
  have hb : y ≤ s.smear ramps b := by
    have := (abs_le.mp (correction_bound s ramps b)).2
    dsimp [Schedule.smear, b] at *
    linarith
  obtain ⟨t, _, ht⟩ :=
    intermediate_value_Icc hab (smear_continuous s ramps).continuousOn ⟨ha, hb⟩
  exact ⟨t, ht⟩

theorem smear_strictMono {k : ℝ} (hk : k < 1)
    (h : ∀ x y : ℝ, x < y → s.correction ramps y - s.correction ramps x ≤ k * (y - x)) :
    StrictMono (s.smear ramps) := by
  intro x y hxy
  have hlt := mul_lt_mul_of_pos_right hk (sub_pos.mpr hxy)
  have := h x y hxy
  unfold Schedule.smear
  linarith

theorem linear_ramp_abs_sub_le {edge left right : ℝ} (hlt : left < right)
    (hl : left ≤ edge) (hr : edge ≤ right) (x y : ℝ) :
    |(Ramp.linear hlt hl hr).value y - (Ramp.linear hlt hl hr).value x| ≤
      |y - x| / (right - left) := by
  let u := (y - left) / (right - left)
  let v := (x - left) / (right - left)
  change |min 1 (max 0 u) - min 1 (max 0 v)| ≤ _
  calc
    _ ≤ |max 0 u - max 0 v| := by
      simpa using abs_min_sub_min_le_max (1 : ℝ) (max 0 u) 1 (max 0 v)
    _ ≤ |u - v| := by
      simpa only [max_comm 0 u, max_comm 0 v] using abs_max_sub_max_le_abs u v 0
    _ = _ := by
      dsimp [u, v]
      rw [← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos (sub_pos.mpr hlt)]

theorem linear_smear_strictMono (before after : Int → ℝ)
    (hb : ∀ d, 0 ≤ before d) (ha : ∀ d, 0 ≤ after d)
    (hw : ∀ d, 0 < before d + after d)
    (hk : (∑ d ∈ s.transitions, 1 / (before d + after d)) < 1) :
    StrictMono (s.smear (s.linearRamps before after hb ha hw)) := by
  apply smear_strictMono s _ hk
  intro x y hxy
  let ramps := s.linearRamps before after hb ha hw
  change s.correction ramps y - s.correction ramps x ≤ _
  unfold Schedule.correction
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro d _
  have hs := linear_ramp_abs_sub_le (ramps d).left_lt_right
    (ramps d).left_le_edge (ramps d).edge_le_right x y
  have hr : (ramps d).right - (ramps d).left = before d + after d := by
    change ((s.midnight d : ℝ) + after d) - (s.midnight d - before d) = _
    ring
  rw [← mul_sub]
  apply (le_abs_self _).trans
  rw [abs_mul, abs_leap, one_mul, div_mul_eq_mul_div, one_mul, ← hr,
    ← abs_of_pos (sub_pos.mpr hxy)]
  exact hs

end Silmaril.Proofs.Numeric.UnixClock
