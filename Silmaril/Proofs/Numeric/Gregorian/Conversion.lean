module

public import Silmaril.Numeric.Gregorian.Defs
import all Std.Time.Date.Unit.Year
import all Std.Time.Date.Unit.Month
import all Std.Time.Internal.UnitVal

/-! Proofs for `Silmaril.Numeric.Gregorian.Thms`. -/

public section

namespace Silmaril.Proofs.Numeric.Gregorian

open Silmaril.Numeric.Gregorian
open Silmaril.Numeric.Gregorian.Internal
open Silmaril.Numeric.Ieee754.Bisection (lastLE lastLE_spec)

theorem isLeapYear_iff (year : Int) :
    isLeapYear year = true ↔ (4 ∣ year ∧ (¬ 100 ∣ year ∨ 400 ∣ year)) := by
  simp only [isLeapYear, Std.Time.Year.Offset.isLeap, Std.Time.Year.Offset.ofInt,
    Std.Time.Year.Offset.toInt, decide_eq_true_eq, Ne, ← Int.dvd_iff_tmod_eq_zero]

private theorem div_step (year divisor : Int) (positive : divisor > 0) :
    year / divisor - (year - 1) / divisor = if divisor ∣ year then 1 else 0 := by
  have lower := Int.emod_nonneg year (by omega : divisor ≠ 0)
  have upper := Int.emod_lt_of_pos year positive
  have splitYear := Int.emod_add_mul_ediv year divisor
  by_cases divisible : divisor ∣ year
  · have remainder := (Int.dvd_iff_emod_eq_zero ..).mp divisible
    rw [ite_eq_left divisible]
    have prev : (year - 1) / divisor = year / divisor - 1 := by
      rw [Int.ediv_eq_iff_of_pos positive, Int.sub_mul, Int.one_mul, Int.mul_comm (year / divisor)]
      omega
    omega
  · have remainder : year % divisor ≠ 0 := mt (Int.dvd_iff_emod_eq_zero ..).mpr divisible
    rw [ite_eq_right divisible]
    have prev : (year - 1) / divisor = year / divisor := by
      rw [Int.ediv_eq_iff_of_pos positive, Int.mul_comm (year / divisor)]
      omega
    omega

theorem yearStart_succ (year : Int) :
    yearStart (year + 1) = yearStart year + daysInYear year := by
  have h4 := div_step year 4 (by decide)
  have h100 := div_step year 100 (by decide)
  have h400 := div_step year 400 (by decide)
  have leap : isLeapYear year = decide ((4 : Int) ∣ year ∧ (¬ 100 ∣ year ∨ 400 ∣ year)) := by
    rw [Bool.eq_iff_iff, decide_eq_true_eq, isLeapYear_iff]
  simp only [yearStart, daysInYear, Int.add_sub_cancel, leap, decide_eq_true_eq]
  by_cases four : (4 : Int) ∣ year
  · by_cases hundred : (100 : Int) ∣ year
    · by_cases fourHundred : (400 : Int) ∣ year <;>
        simp [four, hundred, fourHundred] at h4 h100 h400 ⊢ <;> omega
    · have fourHundred : ¬ (400 : Int) ∣ year :=
        fun hy => hundred (Int.dvd_trans (by decide) hy)
      simp [four, hundred, fourHundred] at h4 h100 h400 ⊢
      omega
  · have hundred : ¬ (100 : Int) ∣ year := fun hy => four (Int.dvd_trans (by decide) hy)
    have fourHundred : ¬ (400 : Int) ∣ year := fun hy => hundred (Int.dvd_trans (by decide) hy)
    simp [four, hundred, fourHundred] at h4 h100 h400 ⊢
    omega

private theorem yearStart_strictMono : StrictMono yearStart := by
  apply strictMono_int_of_lt_succ
  intro year
  rw [yearStart_succ]
  unfold daysInYear
  split <;> omega

theorem yearStart_shift (year eras : Int) :
    yearStart (year + 400 * eras) = yearStart year + 146097 * eras := by
  have h4 : (year + 400 * eras - 1) / 4 = (year - 1) / 4 + 100 * eras := by
    rw [show year + 400 * eras - 1 = year - 1 + 4 * (100 * eras) by omega,
      Int.add_mul_ediv_left _ _ (by decide)]
  have h100 : (year + 400 * eras - 1) / 100 = (year - 1) / 100 + 4 * eras := by
    rw [show year + 400 * eras - 1 = year - 1 + 100 * (4 * eras) by omega,
      Int.add_mul_ediv_left _ _ (by decide)]
  have h400 : (year + 400 * eras - 1) / 400 = (year - 1) / 400 + eras := by
    rw [show year + 400 * eras - 1 = year - 1 + 400 * eras by omega,
      Int.add_mul_ediv_left _ _ (by decide)]
  simp only [yearStart, h4, h100, h400]
  omega

private theorem month_cases (month : Nat) (lower : 1 ≤ month) (upper : month ≤ 12) :
    month = 1 ∨ month = 2 ∨ month = 3 ∨ month = 4 ∨ month = 5 ∨ month = 6 ∨
      month = 7 ∨ month = 8 ∨ month = 9 ∨ month = 10 ∨ month = 11 ∨ month = 12 := by omega

theorem daysInMonth_eq (year : Int) (month : Nat) :
    daysInMonth year month =
      if 1 ≤ month ∧ month ≤ 12 then
        if month = 2 then (if isLeapYear year then 29 else 28)
        else if month = 4 ∨ month = 6 ∨ month = 9 ∨ month = 11 then 30 else 31
      else 0 := by
  by_cases validMonth : 1 ≤ month ∧ month ≤ 12
  · rw [daysInMonth, dite_eq_left validMonth, ite_eq_left validMonth]
    generalize isLeapYear year = leap
    rcases month_cases month validMonth.1 validMonth.2 with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases leap <;> rfl
  · simp only [daysInMonth, dite_eq_right validMonth, ite_eq_right validMonth]

private theorem monthStart_zero (leap : Bool) : monthStart leap 0 = 0 := by
  cases leap <;> rfl

private theorem monthStart_end (year : Int) :
    monthStart (isLeapYear year) 12 = daysInYear year := by
  simp only [monthStart, Nat.lt_irrefl, ↓reduceDIte, daysInYear]
  split <;> rfl

private theorem monthStart_succ (year : Int) (index : Nat) (hi : index < 12) :
    monthStart (isLeapYear year) (index + 1) =
      monthStart (isLeapYear year) index + daysInMonth year (index + 1) := by
  have validMonth : 1 ≤ index + 1 ∧ index + 1 ≤ 12 := by omega
  rw [daysInMonth, dite_eq_left validMonth]
  generalize isLeapYear year = leap
  have indices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨
      index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨ index = 11 := by omega
  rcases indices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases leap <;> rfl

private theorem monthStart_monotone (year : Int) : Monotone (monthStart (isLeapYear year)) := by
  apply monotone_nat_of_le_succ
  intro index
  by_cases hi : index < 12
  · rw [monthStart_succ year index hi]
    omega
  · have next : ¬ index + 1 < 12 := by omega
    simp only [monthStart, hi, next, ↓reduceDIte, le_refl]

private theorem year_bracket (day : Int) :
    yearStart (CivilDate.ofEpochDay day).year ≤ day ∧
      day < yearStart ((CivilDate.ofEpochDay day).year + 1) := by
  let era := (day - yearStart 1) / 146097
  let firstYear := 1 + 400 * era
  have left : yearStart firstYear ≤ day := by
    rw [show firstYear = 1 + 400 * era from rfl, yearStart_shift]
    dsimp only [era]
    omega
  have right : day < yearStart (firstYear + 400) := by
    rw [show firstYear + 400 = 1 + 400 * (era + 1) by dsimp only [firstYear]; omega,
      yearStart_shift]
    dsimp only [era]
    omega
  have right' : day < yearStart (firstYear + (↑(400 : Nat) : Int)) := right
  obtain ⟨_, _, lo, hi⟩ := lastLE_spec (fun index => yearStart (firstYear + index)) day
    0 400 (by decide) (by simpa using left) right'
  refine ⟨lo, ?_⟩
  rw [Int.natCast_add_one, ← Int.add_assoc] at hi
  exact hi

theorem ofEpochDay_year_eq_iff {day year : Int} :
    (CivilDate.ofEpochDay day).year = year ↔ yearStart year ≤ day ∧ day < yearStart (year + 1) := by
  constructor
  · rintro rfl
    exact year_bracket day
  · intro ⟨lo, hi⟩
    obtain ⟨decodedLo, decodedHi⟩ := year_bracket day
    rcases lt_trichotomy (CivilDate.ofEpochDay day).year year with before | same | after
    · have := yearStart_strictMono.monotone (show (CivilDate.ofEpochDay day).year + 1 ≤ year by omega)
      omega
    · exact same
    · have := yearStart_strictMono.monotone (show year + 1 ≤ (CivilDate.ofEpochDay day).year by omega)
      omega

private theorem decode_spec (day : Int) :
    let date := CivilDate.ofEpochDay day
    date.Valid ∧
      yearStart date.year + monthStart (isLeapYear date.year) (date.month - 1) + date.day - 1 = day := by
  let date := CivilDate.ofEpochDay day
  let dayOfYear := day - yearStart date.year
  let leap := isLeapYear date.year
  let monthIndex := lastLE (monthStart leap) dayOfYear 0 12
  obtain ⟨lo, hi⟩ := year_bracket day
  have left : monthStart leap 0 ≤ dayOfYear := by
    rw [monthStart_zero]
    dsimp only [dayOfYear, date]
    omega
  have right : dayOfYear < monthStart leap 12 := by
    change dayOfYear < monthStart (isLeapYear date.year) 12
    rw [monthStart_end]
    rw [yearStart_succ] at hi
    dsimp only [dayOfYear, date]
    omega
  obtain ⟨_, monthBound, monthLow, monthHigh⟩ :=
    lastLE_spec (monthStart leap) dayOfYear 0 12 (by decide) left right
  change monthIndex < 12 at monthBound
  change monthStart leap monthIndex ≤ dayOfYear at monthLow
  change dayOfYear < monthStart (isLeapYear date.year) (monthIndex + 1) at monthHigh
  rw [monthStart_succ date.year monthIndex monthBound] at monthHigh
  have month_eq : date.month = monthIndex + 1 := rfl
  have day_eq : date.day = (dayOfYear - monthStart leap monthIndex + 1).toNat := rfl
  have castDay : (date.day : Int) = dayOfYear - monthStart leap monthIndex + 1 := by
    rw [day_eq, Int.toNat_of_nonneg (by omega)]
  constructor
  · change 1 ≤ date.month ∧ date.month ≤ 12 ∧ 1 ≤ date.day ∧
      date.day ≤ daysInMonth date.year date.month
    rw [month_eq]
    change dayOfYear < monthStart leap monthIndex + daysInMonth date.year (monthIndex + 1) at monthHigh
    exact ⟨by omega, by omega, by omega, by omega⟩
  · rw [month_eq, Nat.add_sub_cancel, castDay]
    change yearStart date.year + monthStart leap monthIndex +
      (dayOfYear - monthStart leap monthIndex + 1) - 1 = day
    dsimp only [dayOfYear]
    omega

theorem ofEpochDay_valid (day : Int) : (CivilDate.ofEpochDay day).Valid := (decode_spec day).1

theorem toEpochDay?_ofEpochDay (day : Int) : (CivilDate.ofEpochDay day).toEpochDay? = some day := by
  rw [CivilDate.toEpochDay?, ite_eq_left (decode_spec day).1, (decode_spec day).2]

theorem epoch_toEpochDay? : (⟨1970, 1, 1⟩ : CivilDate).toEpochDay? = some 0 := by
  have valid : (⟨1970, 1, 1⟩ : CivilDate).Valid := by simp [CivilDate.Valid, daysInMonth_eq]
  have january : yearStart 1970 = 0 := by decide
  simp [CivilDate.toEpochDay?, valid, january, monthStart_zero]

private theorem encode_brackets {date : CivilDate} {day : Int} (h : date.toEpochDay? = some day) :
    (yearStart date.year ≤ day ∧ day < yearStart (date.year + 1)) ∧
      (monthStart (isLeapYear date.year) (date.month - 1) ≤ day - yearStart date.year ∧
        day - yearStart date.year < monthStart (isLeapYear date.year) date.month) ∧
      day = yearStart date.year + monthStart (isLeapYear date.year) (date.month - 1) + date.day - 1 := by
  unfold CivilDate.toEpochDay? at h
  split at h
  next valid =>
    obtain ⟨lowerMonth, upperMonth, lowerDay, upperDay⟩ := valid
    have nextIndex : date.month - 1 + 1 = date.month := by omega
    have step := monthStart_succ date.year (date.month - 1) (by omega)
    rw [nextIndex] at step
    have monthFloor := monthStart_monotone date.year (Nat.zero_le (date.month - 1))
    rw [monthStart_zero] at monthFloor
    have monthCeiling := monthStart_monotone date.year upperMonth
    rw [monthStart_end] at monthCeiling
    rw [yearStart_succ]
    have fields := Option.some.inj h
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, fields.symm⟩
  next => cases h

theorem ofEpochDay_toEpochDay? {date : CivilDate} {day : Int} (h : date.toEpochDay? = some day) :
    CivilDate.ofEpochDay day = date := by
  let decoded := CivilDate.ofEpochDay day
  obtain ⟨_, ⟨ml₁, mh₁⟩, offset₁⟩ := encode_brackets (toEpochDay?_ofEpochDay day)
  obtain ⟨yearBounds, ⟨ml₂, mh₂⟩, offset₂⟩ := encode_brackets h
  have sameYear : decoded.year = date.year := ofEpochDay_year_eq_iff.mpr yearBounds
  change monthStart (isLeapYear decoded.year) (decoded.month - 1) ≤ day - yearStart decoded.year at ml₁
  change day - yearStart decoded.year < monthStart (isLeapYear decoded.year) decoded.month at mh₁
  change day = yearStart decoded.year + monthStart (isLeapYear decoded.year) (decoded.month - 1) +
    decoded.day - 1 at offset₁
  rw [sameYear] at ml₁ mh₁ offset₁
  have sameMonth : decoded.month = date.month := by
    rcases Nat.lt_trichotomy decoded.month date.month with before | same | after
    · have := monthStart_monotone date.year (show decoded.month ≤ date.month - 1 by omega)
      omega
    · exact same
    · have := monthStart_monotone date.year (show date.month ≤ decoded.month - 1 by omega)
      omega
  rw [sameMonth] at offset₁
  have sameDay : decoded.day = date.day := by omega
  exact CivilDate.ext sameYear sameMonth sameDay

/-- The day after the last day of a month is the start of its successor. -/
theorem monthStart_add_daysInMonth (year : Int) (month : Nat)
    (valid : 1 ≤ month ∧ month ≤ 12) :
    yearStart year + monthStart (isLeapYear year) (month - 1) + daysInMonth year month =
      if month = 12 then yearStart (year + 1) + monthStart (isLeapYear (year + 1)) 0
      else yearStart year + monthStart (isLeapYear year) month := by
  have step := monthStart_succ year (month - 1) (by omega)
  rw [show month - 1 + 1 = month by omega] at step
  rw [Int.add_assoc, ← step]
  split
  · subst month
    rw [monthStart_end, monthStart_zero, Int.add_zero, yearStart_succ]
  · rfl

end Silmaril.Proofs.Numeric.Gregorian
