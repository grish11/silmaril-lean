module

import Silmaril.Numeric.UnixInterop.Thms
import Silmaril.Numeric.TimeZone.Thms
import Silmaril.Numeric.UnixClock.Thms
import Silmaril.Numeric.UnixRepresentation.Thms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Kernel-checked examples covering ambiguity at both inverse stages and integer encoding. -/

namespace Silmaril.Numeric.UnixInterop

open Set TimeZone Timestamp UnixClock UnixRepresentation

-- The insertion is at the midnight starting epoch day zero.
private def leapSchedule : UnixClock.Schedule := ⟨0, {0}, fun _ => .positive⟩

private noncomputable def leapClock : Convention := leapSchedule.sharpOn univ

private theorem leapClock_forward (t : leapClock.domain) :
    leapClock.forward t = t.val - UnixClock.Schedule.step 1 t.val := by
  have midnight : leapSchedule.midnight 0 = 1 := by decide +kernel
  change t.val - ((0 : Int) : ℝ) - (∑ d ∈ ({0} : Finset Int), ((1 : Int) : ℝ) *
    UnixClock.Schedule.step (leapSchedule.midnight d) t.val) = _
  norm_num [midnight]

private def foldZone : Rules := .scheduled
  ⟨⟨-1000000000⟩, ⟨2000000000⟩, ⟨0⟩, [⟨⟨1000000000⟩, ⟨-1000000000⟩⟩], by decide +kernel⟩

private theorem fold_candidates : foldZone.candidates ⟨0⟩ = [⟨0⟩, ⟨1000000000⟩] := by
  decide +kernel

private theorem leap_fiber (x y : ℝ) :
    x ∈ leapClock.fiber y ↔ x - UnixClock.Schedule.step 1 x = y := by
  constructor
  · rintro ⟨support, reading⟩
    rwa [leapClock_forward] at reading
  · intro reading
    exact ⟨mem_univ x, (leapClock_forward ⟨x, mem_univ x⟩).trans reading⟩

-- One zone candidate lands in the leap repeat, giving exactly three physical preimages.
private theorem fold_preimages (x : ℝ) :
    x ∈ physicalCandidates leapClock foldZone ⟨0⟩ ↔ x = 0 ∨ x = 1 ∨ x = 2 := by
  have candidates : x ∈ physicalCandidates leapClock foldZone ⟨0⟩ ↔
      x - UnixClock.Schedule.step 1 x = 0 ∨ x - UnixClock.Schedule.step 1 x = 1 := by
    simp [physicalCandidates, fold_candidates, or_and_right, exists_or, leap_fiber,
      unixSeconds, Ticks.denote, TickUnit.nanosecondsPerTick]
  rw [candidates]
  by_cases edge : (1 : ℝ) ≤ x
  · simp only [UnixClock.Schedule.step, ite_eq_left edge]
    constructor
    · rintro (h | h)
      · exact Or.inr (Or.inl (by linarith))
      · exact Or.inr (Or.inr (by linarith))
    · rintro (h | h | h)
      · exfalso; linarith
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
  · simp only [UnixClock.Schedule.step, ite_eq_right edge, sub_zero]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exfalso; linarith
    · rintro (h | h | h)
      · exact Or.inl h
      · exact Or.inr h
      · exfalso; linarith

-- The same three physical inputs produce the local civil midnight at the Unix date.
example (x : ℝ) :
    readCivil? leapClock foldZone ⟨x, mem_univ x⟩ = some (CivilReading.ofWall ⟨0⟩) ↔
      x = 0 ∨ x = 1 ∨ x = 2 := by
  rw [readCivil_eq_some_iff]
  simpa using fold_preimages x

example : exactNanoseconds? (-1 / 1000000000) = some ⟨-1⟩ := by
  rw [exactNanoseconds_eq_some_iff, unixSeconds_nanoseconds_eq_iff]
  norm_num

example : exactNanoseconds? (1 / 2000000000) = none := by
  cases h : exactNanoseconds? (1 / 2000000000) with
  | none => rfl
  | some stamp =>
    have grid := (unixSeconds_nanoseconds_eq_iff stamp _).mp (exactNanoseconds_eq_some_iff.mp h)
    have low : 0 < stamp.ticks := by exact_mod_cast (show (0 : ℝ) < stamp.ticks by linarith)
    have high : stamp.ticks < 1 := by exact_mod_cast (show (stamp.ticks : ℝ) < 1 by linarith)
    omega

private noncomputable def nominalClock : Convention := nominalSchedule.sharpOn univ

-- Compare an Int64 count of seconds with an Int64 count of milliseconds at one instant.
example :
    |unixSeconds (WordFormat.int64.decode .utcInstant .second 1) -
      unixSeconds (WordFormat.int64.decode .utcInstant .millisecond 2250)| < 2 + 1 / 1000 := by
  let t : ↑(leapClock.domain ∩ nominalClock.domain) := ⟨9 / 4, mem_univ _, mem_univ _⟩
  have ga : unixSeconds (⟨1250000000⟩ : UnixTime) = leapClock.forward ⟨t.val, t.property.1⟩ := by
    rw [leapClock_forward]
    norm_num [t, UnixClock.Schedule.step, unixSeconds, Ticks.denote, TickUnit.nanosecondsPerTick]
  have gb : unixSeconds (⟨2250000000⟩ : UnixTime) = nominalClock.forward ⟨t.val, t.property.2⟩ := by
    change _ = nominalSchedule.sharp t.val
    norm_num [nominalSchedule, UnixClock.Schedule.sharp, t, unixSeconds, Ticks.denote,
      TickUnit.nanosecondsPerTick]
  have ea : WordFormat.int64.encode (⟨1250000000⟩ : UnixTime) .second .floor = .ok 1 := by
    exact WordFormat.encode_eq_ok_iff.mpr rfl
  have eb : WordFormat.int64.encode (⟨2250000000⟩ : UnixTime) .millisecond .floor = .ok 2250 := by
    exact WordFormat.encode_eq_ok_iff.mpr rfl
  have bound := wordFloor_discrepancy t ga gb ea eb
  rw [← ga, ← gb] at bound
  norm_num [tickSeconds, unixSeconds, Ticks.denote, TickUnit.nanosecondsPerTick] at bound ⊢
  linarith

end Silmaril.Numeric.UnixInterop
