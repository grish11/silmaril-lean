module

public import Silmaril.Numeric.Gregorian.Defs
import Silmaril.Proofs.Numeric.Gregorian.Conversion

/-! # Validation and signed epoch-day laws for Gregorian civil dates -/

public section

namespace Silmaril.Numeric.Gregorian

/-- Multiples of four are leap years, except centuries that are not multiples of 400. -/
theorem isLeapYear_iff (year : Int) :
    isLeapYear year = true ↔ (4 ∣ year ∧ (¬ 100 ∣ year ∨ 400 ∣ year)) :=
  Proofs.Numeric.Gregorian.isLeapYear_iff year

/-- February follows the leap rule, April, June, September and November have
    30 days, and the remaining valid months have 31 days. -/
theorem daysInMonth_eq (year : Int) (month : Nat) :
    daysInMonth year month =
      if 1 ≤ month ∧ month ≤ 12 then
        if month = 2 then (if isLeapYear year then 29 else 28)
        else if month = 4 ∨ month = 6 ∨ month = 9 ∨ month = 11 then 30 else 31
      else 0 :=
  Proofs.Numeric.Gregorian.daysInMonth_eq year month

/-- Successive January starts are separated by the length of the intervening year. -/
theorem yearStart_succ (year : Int) :
    yearStart (year + 1) = yearStart year + daysInYear year :=
  Proofs.Numeric.Gregorian.yearStart_succ year

/-- Every 400-year shift moves January 1 by 146097 days in the same direction. -/
theorem yearStart_shift (year eras : Int) :
    yearStart (year + 400 * eras) = yearStart year + 146097 * eras :=
  Proofs.Numeric.Gregorian.yearStart_shift year eras

namespace CivilDate

/-- The executable validation check decides the field bounds. -/
theorem valid_iff (date : CivilDate) : date.valid = true ↔ date.Valid := by
  simp [valid]

/-- Encoding rejects exactly the invalid date candidates. -/
theorem toEpochDay?_eq_none_iff (date : CivilDate) : date.toEpochDay? = none ↔ ¬ date.Valid := by
  by_cases h : date.Valid <;> simp [toEpochDay?, h]

/-- January 1, 1970 is the zero of the signed day count. -/
theorem epoch_toEpochDay? : (⟨1970, 1, 1⟩ : CivilDate).toEpochDay? = some 0 :=
  Proofs.Numeric.Gregorian.epoch_toEpochDay?

/-- Every signed day decodes to a valid civil date. -/
theorem ofEpochDay_valid (day : Int) : (ofEpochDay day).Valid :=
  Proofs.Numeric.Gregorian.ofEpochDay_valid day

/-- Decoding and encoding recover the original signed epoch day. -/
theorem toEpochDay?_ofEpochDay (day : Int) : (ofEpochDay day).toEpochDay? = some day :=
  Proofs.Numeric.Gregorian.toEpochDay?_ofEpochDay day

/-- A successfully encoded civil date is recovered by decoding. -/
theorem ofEpochDay_toEpochDay? {date : CivilDate} {day : Int} (h : date.toEpochDay? = some day) :
    ofEpochDay day = date :=
  Proofs.Numeric.Gregorian.ofEpochDay_toEpochDay? h

end CivilDate

end Silmaril.Numeric.Gregorian
