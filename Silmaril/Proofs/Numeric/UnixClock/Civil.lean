module

public import Silmaril.Numeric.UnixClock.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Silmaril.Numeric.Gregorian.Thms

public section

namespace Silmaril.Proofs.Numeric.UnixClock

open Silmaril.Numeric.UnixClock
open Silmaril.Numeric.Gregorian (CivilDate)
open Silmaril.Numeric.Timestamp (Ticks TickUnit)
open Set

variable (s : Schedule)

private theorem seconds_bounds (sign : Leap) : -1 ≤ sign.seconds ∧ sign.seconds ≤ 1 := by
  cases sign <;> decide

theorem dayLength_bounds (d : Int) : 86399 ≤ s.dayLength d ∧ s.dayLength d ≤ 86401 := by
  unfold Schedule.dayLength Schedule.adjustment
  split
  · have := seconds_bounds (s.leap (d + 1))
    omega
  · omega

private theorem offset_succ (d : Int) : s.offset (d + 1) - s.offset d = s.adjustment (d + 1) := by
  classical
  rw [Schedule.offset, Schedule.offset, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  calc
    _ = ∑ i ∈ s.transitions, if i = d + 1 then (s.leap i).seconds else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : i = d + 1
      · subst i
        simp [show ¬ d + 1 ≤ d by omega]
      · by_cases hi : i ≤ d
        · simp [h, hi, show i ≤ d + 1 by omega]
        · simp [h, hi, show ¬ i ≤ d + 1 by omega]
    _ = _ := by simp [Schedule.adjustment, Finset.sum_ite_eq']

theorem midnight_succ (d : Int) : s.midnight (d + 1) = s.midnight d + s.dayLength d := by
  have := offset_succ s d
  unfold Schedule.midnight Schedule.dayLength
  omega

theorem midnight_strictMono : StrictMono s.midnight := by
  apply strictMono_int_of_lt_succ
  intro d
  have := (dayLength_bounds s d).1
  rw [midnight_succ]
  omega

private theorem offset_bound (d : Int) : |s.offset d| ≤ (s.transitions.card : Int) := by
  classical
  rw [Schedule.offset, Finset.sum_filter]
  calc
    |∑ i ∈ s.transitions, if i ≤ d then (s.leap i).seconds else 0| ≤
        ∑ i ∈ s.transitions, |if i ≤ d then (s.leap i).seconds else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s.transitions, (1 : Int) := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs
      · exact abs_le.mpr (seconds_bounds (s.leap i))
      · decide
    _ = _ := by simp

private theorem midnightSet_bounded (t : ℝ) :
    ({d : Int | (s.midnight d : ℝ) ≤ t} : Set Int).Nonempty ∧
      BddAbove {d : Int | (s.midnight d : ℝ) ≤ t} := by
  obtain ⟨m, hm⟩ := exists_int_gt (|t| + |(s.baseline : ℝ)| + s.transitions.card)
  have hm0 : (0 : ℝ) < m :=
    lt_of_le_of_lt (add_nonneg (add_nonneg (abs_nonneg t) (abs_nonneg _)) (Nat.cast_nonneg _)) hm
  have bound (d : Int) : |(s.offset d : ℝ)| ≤ s.transitions.card := by
    exact_mod_cast offset_bound s d
  have low : (s.midnight (-m) : ℝ) ≤ t := by
    have h := (abs_le.mp (bound (-m))).2
    have hb := le_abs_self (s.baseline : ℝ)
    have ht := neg_abs_le t
    push_cast [Schedule.midnight]
    linarith
  have high : t < (s.midnight m : ℝ) := by
    have h := (abs_le.mp (bound m)).1
    have hb := neg_abs_le (s.baseline : ℝ)
    have ht := le_abs_self t
    push_cast [Schedule.midnight]
    linarith
  refine ⟨⟨-m, low⟩, ⟨m, ?_⟩⟩
  intro d hd
  by_contra! h
  have h' : (s.midnight m : ℝ) < s.midnight d :=
    Int.cast_lt.mpr (midnight_strictMono s h)
  exact (not_lt_of_ge hd) (high.trans h')

theorem dayAt_spec (t : ℝ) :
    (s.midnight (s.dayAt t) : ℝ) ≤ t ∧ t < s.midnight (s.dayAt t + 1) := by
  obtain ⟨hne, hbd⟩ := midnightSet_bounded s t
  constructor
  · exact Int.csSup_mem hne hbd
  · by_contra! h
    have h' : s.dayAt t + 1 ≤ s.dayAt t := le_csSup hbd h
    omega

theorem dayAt_eq_iff {t : ℝ} {d : Int} :
    s.dayAt t = d ↔ (s.midnight d : ℝ) ≤ t ∧ t < s.midnight (d + 1) := by
  constructor
  · rintro rfl
    exact dayAt_spec s t
  · intro ⟨hl, hu⟩
    have hs := dayAt_spec s t
    apply le_antisymm
    · by_contra! h
      have h' : d + 1 ≤ s.dayAt t := by omega
      exact (not_lt_of_ge (le_trans (Int.cast_le.mpr ((midnight_strictMono s).monotone h')) hs.1)) hu
    · by_contra! h
      have h' : s.dayAt t + 1 ≤ d := by omega
      exact (not_lt_of_ge (le_trans (Int.cast_le.mpr ((midnight_strictMono s).monotone h')) hl)) hs.2

theorem toTAI_eq_some_iff {label : CivilLabel} {t : ℝ} :
    s.toTAI? label = some t ↔
      ∃ d, label.date.toEpochDay? = some d ∧ s.validSecond d label.secondOfDay ∧
        t = (s.midnight d : ℝ) + label.secondOfDay := by
  cases h : label.date.toEpochDay? with
  | none => simp [Schedule.toTAI?, h]
  | some d =>
    by_cases hvalid : s.validSecond d label.secondOfDay <;>
      simp [Schedule.toTAI?, h, hvalid, eq_comm]

private theorem interval_of_validSecond {d : Int} {u : ℝ} (h : s.validSecond d u) :
    (s.midnight d : ℝ) ≤ (s.midnight d : ℝ) + u ∧
      (s.midnight d : ℝ) + u < (s.midnight (d + 1) : ℝ) := by
  obtain ⟨hl, hu⟩ := h
  rw [midnight_succ, Int.cast_add]
  constructor <;> linarith

theorem toTAI_ofTAI (t : ℝ) : s.toTAI? (s.ofTAI t) = some t := by
  obtain ⟨hl, hu⟩ := dayAt_spec s t
  rw [midnight_succ, Int.cast_add] at hu
  apply (toTAI_eq_some_iff s).mpr
  refine ⟨s.dayAt t, CivilDate.toEpochDay?_ofEpochDay _, ⟨?_, ?_⟩, ?_⟩
  · exact sub_nonneg.mpr hl
  · exact sub_lt_iff_lt_add.mpr (by simpa [add_comm] using hu)
  · linarith [show (s.ofTAI t).secondOfDay = t - s.midnight (s.dayAt t) from rfl]

theorem ofTAI_toTAI {label : CivilLabel} {t : ℝ} (h : s.toTAI? label = some t) :
    s.ofTAI t = label := by
  obtain ⟨d, hd, hu, rfl⟩ := (toTAI_eq_some_iff s).mp h
  have hday := (dayAt_eq_iff s).mpr (interval_of_validSecond s hu)
  unfold Schedule.ofTAI
  rw [hday, CivilDate.ofEpochDay_toEpochDay? hd, add_sub_cancel_left]

theorem sharp_of_validSecond {d : Int} {u : ℝ} (h : s.validSecond d u) :
    s.sharp ((s.midnight d : ℝ) + u) = (d : ℝ) * 86400 + u := by
  obtain ⟨hl, hu⟩ := interval_of_validSecond s h
  have step_eq (i : Int) :
      Schedule.step (s.midnight i) ((s.midnight d : ℝ) + u) = if i ≤ d then 1 else 0 := by
    unfold Schedule.step
    by_cases hi : i ≤ d
    · simp [hi, (Int.cast_le.mpr ((midnight_strictMono s).monotone hi)).trans hl]
    · have hdi : d + 1 ≤ i := by omega
      simp [hi, not_le.mpr (hu.trans_le (Int.cast_le.mpr ((midnight_strictMono s).monotone hdi)))]
  unfold Schedule.sharp
  simp_rw [step_eq, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  have hoff : (s.offset d : ℝ) =
      ∑ i ∈ s.transitions.filter (· ≤ d), ((s.leap i).seconds : ℝ) := by
    exact Int.cast_sum _ _
  rw [← hoff]
  push_cast [Schedule.midnight]
  ring

theorem sharp_toTAI {label : CivilLabel} {t : ℝ} {d : Int}
    (h : s.toTAI? label = some t) (hd : label.date.toEpochDay? = some d) :
    s.sharp t = (d : ℝ) * 86400 + label.secondOfDay := by
  obtain ⟨d', hd', hu, rfl⟩ := (toTAI_eq_some_iff s).mp h
  rw [hd] at hd'
  cases hd'
  exact sharp_of_validSecond s hu

theorem civilToUnix_eq_some_iff {label : CivilLabel} {y : ℝ} :
    civilToUnix? label = some y ↔
      ∃ d : Int, label.date.toEpochDay? = some d ∧ 0 ≤ label.secondOfDay ∧
        label.secondOfDay < 86400 ∧ y = (d : ℝ) * 86400 + label.secondOfDay := by
  rw [civilToUnix?, toTAI_eq_some_iff]
  simp [nominalSchedule, Schedule.midnight, Schedule.offset, Schedule.validSecond,
    Schedule.dayLength, Schedule.adjustment, and_assoc]

theorem civilToUnix_epoch : civilToUnix? unixEpoch = some 0 := by
  apply civilToUnix_eq_some_iff.mpr
  refine ⟨0, CivilDate.epoch_toEpochDay?, le_rfl, ?_, ?_⟩ <;>
    norm_num [unixEpoch]

theorem unixSeconds_whole (ticks : Int) :
    unixSeconds (⟨ticks⟩ : Ticks .utcInstant .second) = (ticks : ℝ) := by
  simp [unixSeconds, Ticks.denote, TickUnit.nanosecondsPerTick]

theorem unixSeconds_nanoseconds_eq_iff (stamp : Ticks .utcInstant .nanosecond) (seconds : ℝ) :
    unixSeconds stamp = seconds ↔ (stamp.ticks : ℝ) = seconds * 1000000000 := by
  simpa [unixSeconds, Ticks.denote, TickUnit.nanosecondsPerTick] using
    (div_eq_iff (by norm_num : (1000000000 : ℝ) ≠ 0) :
      (stamp.ticks : ℝ) / 1000000000 = seconds ↔ (stamp.ticks : ℝ) = seconds * 1000000000)

theorem existsUnique_unixSeconds_nanosecond_iff (seconds : ℝ) :
    (∃! stamp : Ticks .utcInstant .nanosecond, unixSeconds stamp = seconds) ↔
      ∃ ticks : Int, (ticks : ℝ) = seconds * 1000000000 := by
  constructor
  · rintro ⟨stamp, h, _⟩
    exact ⟨stamp.ticks, (unixSeconds_nanoseconds_eq_iff stamp seconds).mp h⟩
  · rintro ⟨n, hn⟩
    refine ⟨⟨n⟩, (unixSeconds_nanoseconds_eq_iff ⟨n⟩ seconds).mpr hn, ?_⟩
    rintro ⟨m⟩ hm
    have hcast := ((unixSeconds_nanoseconds_eq_iff ⟨m⟩ seconds).mp hm).trans hn.symm
    exact congrArg (fun k : Int => (⟨k⟩ : Ticks .utcInstant .nanosecond)) (Int.cast_injective hcast)

theorem iersToTAI_eq_some_iff {label : CivilLabel} {t : ℝ} :
    iersToTAI? label = some t ↔ t ∈ iersDomain ∧ iersSchedule.toTAI? label = some t := by
  cases h : iersSchedule.toTAI? label with
  | none => simp [iersToTAI?, h]
  | some x =>
    unfold iersToTAI?
    rw [h]
    change (if x ∈ iersDomain then some x else none) = some t ↔
      t ∈ iersDomain ∧ some x = some t
    by_cases hx : x ∈ iersDomain
    · simpa only [ite_eq_left hx, Option.some.injEq] using
        (show x = t ↔ t ∈ iersDomain ∧ x = t from ⟨fun e => ⟨e ▸ hx, e⟩, And.right⟩)
    · simpa only [ite_eq_right hx, reduceCtorEq, Option.some.injEq, false_iff] using
        (show ¬ (t ∈ iersDomain ∧ x = t) from fun ⟨ht, e⟩ => hx (e.symm ▸ ht))

theorem iersOfTAI_eq_some_iff {label : CivilLabel} {t : ℝ} :
    iersOfTAI? t = some label ↔ t ∈ iersDomain ∧ iersSchedule.ofTAI t = label := by
  by_cases ht : t ∈ iersDomain <;> simp [iersOfTAI?, ht]

theorem sharp_eq_of_dayAt (t : ℝ) :
    s.sharp t = (s.dayAt t : ℝ) * 86400 + (t - s.midnight (s.dayAt t)) := by
  exact sharp_toTAI s (toTAI_ofTAI s t) (CivilDate.toEpochDay?_ofEpochDay _)

theorem tai_sub_sharp (t : ℝ) : t - s.sharp t = (s.taiMinusUTC t : ℝ) := by
  rw [sharp_eq_of_dayAt]
  push_cast [Schedule.taiMinusUTC, Schedule.midnight]
  ring

theorem sharpOn_injective_of_subset_day {domain : Set ℝ} {d : Int}
    (h : domain ⊆ Ico (s.midnight d : ℝ) (s.midnight (d + 1) : ℝ)) :
    Function.Injective (s.sharpOn domain).forward := by
  intro x y he
  apply Subtype.ext
  change s.sharp x.val = s.sharp y.val at he
  rw [sharp_eq_of_dayAt s x.val, sharp_eq_of_dayAt s y.val,
    (dayAt_eq_iff s).mpr (h x.property), (dayAt_eq_iff s).mpr (h y.property)] at he
  linarith

/-- For an ordinary nominal reading, the only candidates are its own date and
    the extended final second of the preceding date. -/
theorem mem_sharp_fiber_iff {domain : Set ℝ} {t : ℝ} {d : Int} {u : ℝ}
    (hu : u ∈ Ico (0 : ℝ) 86400) :
    t ∈ (s.sharpOn domain).fiber ((d : ℝ) * 86400 + u) ↔
      t ∈ domain ∧
        ((s.validSecond d u ∧ t = (s.midnight d : ℝ) + u) ∨
          (s.validSecond (d - 1) (86400 + u) ∧
            t = (s.midnight (d - 1) : ℝ) + (86400 + u))) := by
  constructor
  · rintro ⟨ht, he⟩
    refine ⟨ht, ?_⟩
    obtain ⟨i, hi, hv, htime⟩ := (toTAI_eq_some_iff s).mp (toTAI_ofTAI s t)
    let v := (s.ofTAI t).secondOfDay
    have eq : (i : ℝ) * 86400 + v = (d : ℝ) * 86400 + u :=
      (sharp_toTAI s (toTAI_ofTAI s t) hi).symm.trans he
    have hv0 : 0 ≤ v := hv.1
    have hv1 : v < 86401 := hv.2.trans_le (by exact_mod_cast (dayLength_bounds s i).2)
    obtain ⟨hu0, hu1⟩ := hu
    have upper : i ≤ d := by
      by_contra! hn
      have hb : (d : ℝ) + 1 ≤ i := by exact_mod_cast (show d + 1 ≤ i by omega)
      linarith
    have lower : d - 1 ≤ i := by
      by_contra! hn
      have hb : (i : ℝ) + 2 ≤ d := by exact_mod_cast (show i + 2 ≤ d by omega)
      linarith
    rcases (show i = d ∨ i = d - 1 by omega) with rfl | rfl
    · have hvu : v = u := by linarith
      exact Or.inl ⟨hvu ▸ hv, hvu ▸ htime⟩
    · have hvu : v = 86400 + u := by push_cast at eq; linarith
      exact Or.inr ⟨hvu ▸ hv, hvu ▸ htime⟩
  · rintro ⟨ht, ⟨hv, rfl⟩ | ⟨hv, rfl⟩⟩
    · exact ⟨ht, sharp_of_validSecond s hv⟩
    · refine ⟨ht, ?_⟩
      change s.sharp _ = _
      rw [sharp_of_validSecond s hv]
      push_cast
      ring

theorem positive_fiber {domain : Set ℝ} {t : ℝ} {d : Int} {f : ℝ}
    (h : s.adjustment d = 1) (hf : f ∈ Ico (0 : ℝ) 1) :
    t ∈ (s.sharpOn domain).fiber ((d : ℝ) * 86400 + f) ↔
      t ∈ domain ∧
        (t = (s.midnight d : ℝ) + f ∨ t = (s.midnight d : ℝ) - 1 + f) := by
  obtain ⟨hf0, hf1⟩ := hf
  have hdlen : (1 : ℝ) ≤ s.dayLength d := by
    exact_mod_cast ((show (1 : Int) ≤ 86399 by decide).trans (dayLength_bounds s d).1)
  have hd : s.validSecond d f := ⟨hf0, hf1.trans_le hdlen⟩
  have hlen : s.dayLength (d - 1) = 86401 := by
    simp [Schedule.dayLength, h]
  have hprev : s.validSecond (d - 1) (86400 + f) := by
    unfold Schedule.validSecond
    rw [hlen]
    norm_num
    constructor <;> linarith
  have hmid := midnight_succ s (d - 1)
  rw [sub_add_cancel, hlen] at hmid
  have hmid' : (s.midnight d : ℝ) = (s.midnight (d - 1) : ℝ) + 86401 := by
    exact_mod_cast hmid
  rw [mem_sharp_fiber_iff s (show f ∈ Ico (0 : ℝ) 86400 from ⟨hf0, hf1.trans (by norm_num)⟩)]
  simp only [hd, hprev, true_and]
  have he : (s.midnight (d - 1) : ℝ) + (86400 + f) = (s.midnight d : ℝ) - 1 + f := by
    linarith
  rw [he]

theorem negative_fiber {domain : Set ℝ} {d : Int} {f : ℝ}
    (h : s.adjustment d = -1) (hf : f ∈ Ico (0 : ℝ) 1) :
    (s.sharpOn domain).fiber (((d : ℝ) - 1) * 86400 + (86399 + f)) = ∅ := by
  obtain ⟨hf0, hf1⟩ := hf
  have hu : 86399 + f ∈ Ico (0 : ℝ) 86400 := ⟨by linarith, by linarith⟩
  have hlen : s.dayLength (d - 1) = 86399 := by
    simp [Schedule.dayLength, h]
  have hbad : ¬ s.validSecond (d - 1) (86399 + f) := by
    intro hv
    have hvlt := hv.2
    rw [hlen] at hvlt
    norm_num at hvlt
    linarith
  have hbadPrev : ¬ s.validSecond (d - 1 - 1) (86400 + (86399 + f)) := by
    intro hv
    have hb : (s.dayLength (d - 1 - 1) : ℝ) ≤ 86401 := by
      exact_mod_cast (dayLength_bounds s (d - 1 - 1)).2
    linarith [hv.2]
  ext t
  rw [← Int.cast_one, ← Int.cast_sub, mem_sharp_fiber_iff s hu]
  simp [hbad, hbadPrev]

end Silmaril.Proofs.Numeric.UnixClock
