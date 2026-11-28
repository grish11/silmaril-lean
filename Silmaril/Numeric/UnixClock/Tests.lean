module

import Silmaril.Numeric.UnixClock.Thms
import Silmaril.Numeric.Gregorian.Thms
import Silmaril.Numeric.Timestamp.Thms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
-- Expose Std's calendar arithmetic for kernel reduction of the Gregorian test dates.
import all Std.Time.Date.Unit.Year
import all Std.Time.Date.Unit.Month
import all Std.Time.Internal.UnitVal

/-! # Kernel-checked Unix clock examples -/

namespace Silmaril.Numeric.UnixClock

open Set
open Gregorian (CivilDate)
open scoped ENNReal

noncomputable section

example : civilToUnix? unixEpoch = some 0 := civilToUnix_epoch

example : unixToCivil (-1 / 2) = ⟨⟨1969, 12, 31⟩, 86399 + 1 / 2⟩ := by
  apply unixToCivil_civilToUnix
  refine civilToUnix_eq_some_iff.mpr ⟨-1, by decide +kernel, ?_, ?_, ?_⟩ <;> norm_num

example : unixSeconds (⟨-500⟩ : Timestamp.Ticks .utcInstant .millisecond) = -1 / 2 := by
  norm_num [unixSeconds, Timestamp.Ticks.denote, Timestamp.TickUnit.nanosecondsPerTick]

example :
    unixSeconds (⟨-500⟩ : Timestamp.Ticks .utcInstant .millisecond) =
      unixSeconds (⟨-500000⟩ : Timestamp.Ticks .utcInstant .microsecond) := by
  apply unixSeconds_eq_of_denote_eq
  apply Timestamp.Ticks.rescale_eq_some_iff.mp
  decide +kernel

example :
    unixSeconds (⟨-1⟩ : Timestamp.Ticks .utcInstant .nanosecond) = -1 / 1000000000 := by
  apply (unixSeconds_nanoseconds_eq_iff _ _).mpr
  norm_num

example : ¬ ∃ stamp : Timestamp.Ticks .utcInstant .nanosecond,
    unixSeconds stamp = 1 / 2000000000 := by
  rintro ⟨stamp, h⟩
  have hn := (unixSeconds_nanoseconds_eq_iff stamp _).mp h
  have h0 : (0 : ℝ) < stamp.ticks := by linarith
  have h1 : (stamp.ticks : ℝ) < 1 := by linarith
  have hi0 : (0 : Int) < stamp.ticks := by exact_mod_cast h0
  have hi1 : stamp.ticks < (1 : Int) := by exact_mod_cast h1
  omega

private def iersRows : List (CivilDate × Int) :=
  [(⟨1972, 1, 1⟩, 10), (⟨1972, 7, 1⟩, 11), (⟨1973, 1, 1⟩, 12), (⟨1974, 1, 1⟩, 13),
   (⟨1975, 1, 1⟩, 14), (⟨1976, 1, 1⟩, 15), (⟨1977, 1, 1⟩, 16), (⟨1978, 1, 1⟩, 17),
   (⟨1979, 1, 1⟩, 18), (⟨1980, 1, 1⟩, 19), (⟨1981, 7, 1⟩, 20), (⟨1982, 7, 1⟩, 21),
   (⟨1983, 7, 1⟩, 22), (⟨1985, 7, 1⟩, 23), (⟨1988, 1, 1⟩, 24), (⟨1990, 1, 1⟩, 25),
   (⟨1991, 1, 1⟩, 26), (⟨1992, 7, 1⟩, 27), (⟨1993, 7, 1⟩, 28), (⟨1994, 7, 1⟩, 29),
   (⟨1996, 1, 1⟩, 30), (⟨1997, 7, 1⟩, 31), (⟨1999, 1, 1⟩, 32), (⟨2006, 1, 1⟩, 33),
   (⟨2009, 1, 1⟩, 34), (⟨2012, 7, 1⟩, 35), (⟨2015, 7, 1⟩, 36), (⟨2017, 1, 1⟩, 37)]

-- Check all published offsets against Gregorian dates, and that no extra transitions are present.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
example : (iersRows.map fun row => row.1.toEpochDay?.map fun day =>
    iersSchedule.baseline + iersSchedule.offset day) = iersRows.map (some ∘ Prod.snd) := by
  decide +kernel

set_option maxRecDepth 4096 in
example : iersSchedule.transitions =
    (iersRows.drop 1 |>.filterMap fun row => row.1.toEpochDay?).toFinset := by
  decide +kernel

example : (⟨1972, 1, 1⟩ : CivilDate).toEpochDay? = some iersFirstDay := by decide +kernel
example : (⟨2027, 6, 28⟩ : CivilDate).toEpochDay? = some iersEndDay := by decide +kernel

private theorem firstMidnight : iersSchedule.midnight iersFirstDay = 63072010 := by decide +kernel
private theorem endMidnight : iersSchedule.midnight iersEndDay = 1814140837 := by decide +kernel
private theorem lastLeapMidnight : iersSchedule.midnight 17166 = 1483142436 := by decide +kernel
private theorem afterLastLeap : iersSchedule.midnight 17167 = 1483228837 := by decide +kernel

example : iersOfTAI? 63072009 = none := by
  norm_num [iersOfTAI?, iersDomain, firstMidnight]

example : iersOfTAI? 1814140837 = none := by
  simp [iersOfTAI?, iersDomain, endMidnight]

example : iersToTAI? unixEpoch = none := by
  cases h : iersToTAI? unixEpoch with
  | none => rfl
  | some t =>
    have ⟨ht, h⟩ := iersToTAI_eq_some_iff.mp h
    obtain ⟨d, hd, _, rfl⟩ := iersSchedule.toTAI_eq_some_iff.mp h
    have hd' : d = 0 := Option.some.inj
      (hd.symm.trans (show unixEpoch.date.toEpochDay? = some 0 from CivilDate.epoch_toEpochDay?))
    subst d
    have h0 : iersSchedule.midnight 0 = 10 := by decide +kernel
    norm_num [iersDomain, firstMidnight, h0, unixEpoch] at ht

-- The leap label 23:59:60.5 belongs to 2016-12-31 and round-trips.
example : iersOfTAI? (1483228836 + 1 / 2) = some ⟨⟨2016, 12, 31⟩, 86400 + 1 / 2⟩ := by
  apply iers_roundtrip.mp
  refine iersToTAI_eq_some_iff.mpr ⟨?_, iersSchedule.toTAI_eq_some_iff.mpr ?_⟩
  · norm_num [iersDomain, firstMidnight, endMidnight]
  · have hlen : iersSchedule.dayLength 17166 = 86401 := by decide +kernel
    refine ⟨17166, by decide +kernel, ?_, ?_⟩ <;>
      norm_num [Schedule.validSecond, hlen, lastLeapMidnight]

-- The old offset remains in effect during the leap second.
example : iersTAIMinusUTC? (1483228836 + 1 / 2) = some 36 := by
  apply iersTAIMinusUTC_eq_some_iff.mpr
  refine ⟨by norm_num [iersDomain, firstMidnight, endMidnight], ?_⟩
  have hday : iersSchedule.dayAt (1483228836 + 1 / 2) = 17166 := by
    apply iersSchedule.dayAt_eq_iff.mpr
    norm_num [lastLeapMidnight, afterLastLeap]
  rw [Schedule.taiMinusUTC, hday]
  decide +kernel

example : iersTAIMinusUTC? 1483228837 = some 37 := by
  apply iersTAIMinusUTC_eq_some_iff.mpr
  refine ⟨by norm_num [iersDomain, firstMidnight, endMidnight], ?_⟩
  have nextMidnight : iersSchedule.midnight 17168 = 1483315237 := by decide +kernel
  have hday : iersSchedule.dayAt 1483228837 = 17167 :=
    iersSchedule.dayAt_eq_iff.mpr (by norm_num [afterLastLeap, nextMidnight])
  rw [Schedule.taiMinusUTC, hday]
  decide +kernel

-- The POSIX-shaped reading has two distinct physical preimages.
example (t : ℝ) :
    t ∈ iersUnix.fiber (1483228800 + 1 / 2) ↔
      t = 1483228837 + 1 / 2 ∨ t = 1483228836 + 1 / 2 := by
  have hn : ((17167 : Int) : ℝ) * 86400 = 1483228800 := by norm_num
  rw [← hn]
  change t ∈ (iersSchedule.sharpOn iersDomain).fiber _ ↔ _
  rw [iersSchedule.positive_fiber (show iersSchedule.adjustment 17167 = 1 by decide +kernel)
    (show (1 / 2 : ℝ) ∈ Ico 0 1 by norm_num), afterLastLeap]
  norm_num
  rintro (rfl | rfl) <;> norm_num [iersDomain, firstMidnight, endMidnight]

private def single (sign : Leap) : Schedule := ⟨0, {1}, fun _ => sign⟩

-- At a hypothetical negative leap, final seconds of the preceding nominal day are missing.
example : ((single .negative).sharpOn univ).fiber (86399 + 1 / 2) = ∅ := by
  have h := (single .negative).negative_fiber (domain := univ) (d := 1)
    (show (single .negative).adjustment 1 = -1 by decide +kernel)
    (show (1 / 2 : ℝ) ∈ Ico 0 1 by norm_num)
  norm_num at h ⊢
  exact h

private def repeatedReading : Set ℝ := Ico 86400 86401

-- Choose either branch explicitly, with the selection law on the repeated second.
private def foldResolver (branch : ℝ) (hbranch : branch = 0 ∨ branch = 1) :
    ((single .positive).sharpOn univ).Resolver where
  domain := repeatedReading
  resolve y := ⟨y.val + branch, mem_univ _⟩
  forward_resolve y := by
    have hh : (single .positive).adjustment 1 = 1 := by decide +kernel
    have hm : (single .positive).midnight 1 = 86401 := by decide +kernel
    have hlow : 86400 ≤ y.val := y.property.1
    have hhigh : y.val < 86401 := y.property.2
    have hf : y.val - 86400 ∈ Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have h := (single .positive).positive_fiber (domain := univ) (t := y.val + branch) hh hf
    norm_num [hm] at h
    have he := h.mpr (by
      rcases hbranch with rfl | rfl
      · right
        linarith
      · left
        linarith)
    obtain ⟨_, he⟩ := he
    change (single .positive).sharp (y.val + branch) = _ at he ⊢
    linarith

example : (foldResolver 0 (Or.inl rfl)).worstError (foldResolver 1 (Or.inr rfl)) = 1 := by
  let earlier := foldResolver 0 (Or.inl rfl)
  let later := foldResolver 1 (Or.inr rfl)
  have hsample (y : ℝ) : ENNReal.ofReal |y + 0 - (y + 1)| = 1 := by
    have he : y + 0 - (y + 1) = -1 := by linarith
    norm_num [he]
  change earlier.worstError later = 1
  apply le_antisymm
  · apply (Convention.Resolver.worstError_le_iff _ _ _).mpr
    intro y _ _
    exact (hsample y).le
  · have hy : (86400 : ℝ) ∈ repeatedReading := by norm_num [repeatedReading]
    have he := (Convention.Resolver.worstError_le_iff earlier later _).mp le_rfl 86400 hy hy
    change ENNReal.ofReal |86400 + 0 - (86400 + 1)| ≤ earlier.worstError later at he
    rwa [hsample] at he

private def afterTwo (s : Schedule) : s.Ramps :=
  s.linearRamps (fun _ => 0) (fun _ => 2) (by norm_num) (by norm_num) (by norm_num)

example : StrictMono ((single .positive).smear (afterTwo (single .positive))) := by
  apply (single .positive).linear_smear_strictMono
  norm_num [single]

-- The step at t = 86401 sees the new offset, while a ramp starting there is still zero.
example :
    ((single .positive).smearOn (afterTwo (single .positive)) univ).worstError
      ((single .positive).sharpOn univ) = 1 := by
  let s := single .positive
  let r := afterTwo s
  have hle : (s.smearOn r univ).worstError (s.sharpOn univ) ≤ 1 := by
    apply s.smear_worstError_le_one
    simp [s, single]
  have hmid : s.midnight 1 = 86401 := by decide +kernel
  have hsample : |s.smear r (s.midnight 1) - s.sharp (s.midnight 1)| = 1 := by
    apply s.smear_error_at_left_edge
    · norm_num [s, r, single, afterTwo, Schedule.active, Schedule.linearRamps, Ramp.linear,
        Ramp.window, hmid]
    · simp [r, afterTwo, Schedule.linearRamps, Ramp.linear]
  apply le_antisymm hle
  simpa [Schedule.smearOn, Schedule.sharpOn, hsample] using
    (Convention.worstError_le_iff (s.smearOn r univ) (s.sharpOn univ) _).mp le_rfl
      (s.midnight 1) (mem_univ _) (mem_univ _)

private def oneSecond (s : Schedule) : s.Ramps :=
  s.linearRamps (fun _ => 0) (fun _ => 1) (by norm_num) (by norm_num) (by norm_num)

-- A positive one-second ramp over a one-second window can flatten the clock.
example : ¬ Function.Injective ((single .positive).smear (oneSecond (single .positive))) := by
  intro hinj
  have hmid : (⟨0, {1}, fun _ => .positive⟩ : Schedule).midnight 1 = 86401 := by
    decide +kernel
  have h : ((single .positive).smear (oneSecond (single .positive))) 86401 =
      ((single .positive).smear (oneSecond (single .positive))) 86402 := by
    norm_num [Schedule.smear, Schedule.correction, oneSecond, Schedule.linearRamps, Ramp.linear,
      single, Leap.seconds, hmid]
  exact (by norm_num : (86401 : ℝ) ≠ 86402) (hinj h)

private def doublePositive : Schedule := ⟨0, {1, 2}, fun _ => .positive⟩

private def overlapping : doublePositive.Ramps :=
  doublePositive.linearRamps (fun _ => 0) (fun _ => 172802)
    (by norm_num) (by norm_num) (by norm_num)

-- At the second cut, the first ramp is only halfway through. Both errors have the same sign.
example : |doublePositive.smear overlapping 172802 - doublePositive.sharp 172802| = 3 / 2 := by
  have h1 : (⟨0, {1, 2}, fun _ => .positive⟩ : Schedule).midnight 1 = 86401 := by
    decide +kernel
  have h2 : (⟨0, {1, 2}, fun _ => .positive⟩ : Schedule).midnight 2 = 172802 := by
    decide +kernel
  norm_num [Schedule.smear, Schedule.sharp, Schedule.correction, Schedule.step, overlapping,
    Schedule.linearRamps, Ramp.linear, doublePositive, Leap.seconds, Finset.sum_insert, h1, h2]

private def identityOn (domain : Set ℝ) : Convention := ⟨domain, Subtype.val⟩
private def zeroOn (domain : Set ℝ) : Convention := ⟨domain, fun _ => 0⟩

example : (identityOn univ).worstError (zeroOn ∅) = 0 :=
  Convention.worstError_empty disjoint_bot_right

example : (identityOn univ).worstError (zeroOn univ) = ∞ := by
  apply (Convention.worstError_eq_top_iff _ _).mpr
  intro b hb
  refine ⟨b + 1, mem_univ _, mem_univ _, ?_⟩
  change b < |b + 1 - 0|
  rw [sub_zero, abs_of_nonneg (by linarith)]
  linarith

-- Even a finite supremum need not occur on the common support.
example :
    let d := Ioo (0 : ℝ) 1
    (identityOn d).worstError (zeroOn univ) = 1 ∧
      ∀ t ∈ d, ENNReal.ofReal |t| < 1 := by
  dsimp only
  have hsample (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : ENNReal.ofReal |t| < 1 := by
    rw [ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) (by simp), ENNReal.toReal_one,
      abs_of_pos ht.1]
    exact ht.2
  refine ⟨le_antisymm ((Convention.worstError_le_iff _ _ _).mpr fun t ht _ => ?_) ?_, hsample⟩
  · simpa [identityOn, zeroOn] using (hsample t ht).le
  · let w := (identityOn (Ioo (0 : ℝ) 1)).worstError (zeroOn univ)
    change 1 ≤ w
    by_contra! hw
    have hfin : w ≠ ∞ := ne_top_of_lt hw
    have hw1 : w.toReal < 1 := by simpa using ENNReal.toReal_lt_toReal hfin (by simp) |>.mpr hw
    let t := (w.toReal + 1) / 2
    have ht : t ∈ Ioo (0 : ℝ) 1 := ⟨by dsimp [t]; linarith [ENNReal.toReal_nonneg (a := w)],
      by dsimp [t]; linarith⟩
    have hle : ENNReal.ofReal |t| ≤ w := by
      simpa [identityOn, zeroOn] using
        (Convention.worstError_le_iff _ _ _).mp (le_refl w) t ht (mem_univ t)
    have h := (ENNReal.ofReal_le_iff_le_toReal hfin).mp hle
    rw [abs_of_pos ht.1] at h
    dsimp [t] at h
    linarith

end

end Silmaril.Numeric.UnixClock
