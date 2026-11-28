module

public import Std.Time.Date.Unit.Year
public import Silmaril.Numeric.Ieee754.Bisection

/-! # Proleptic Gregorian civil dates

Years are unbounded integers in astronomical numbering. Year 0 is 1 BCE,
and year −1 is 2 BCE. The same month and leap-year rules apply in every year.
Signed epoch days are relative to 1970-01-01, with that date at day 0.
-/

@[expose] public section

namespace Silmaril.Numeric.Gregorian

/-- The Gregorian leap-year rule on astronomical years. -/
def isLeapYear (year : Int) : Bool := (Std.Time.Year.Offset.ofInt year).isLeap

/-- The number of days in a Gregorian year. -/
def daysInYear (year : Int) : Nat := if isLeapYear year then 366 else 365

/-- The length of a 1-based month, or zero outside 1–12. -/
def daysInMonth (year : Int) (month : Nat) : Nat :=
  if h : 1 ≤ month ∧ month ≤ 12 then
    let ordinal : Std.Time.Month.Ordinal := ⟨month, by omega⟩
    (ordinal.days (isLeapYear year)).toNat
  else 0

/-- The signed epoch day of January 1 of `year`. January 1 of 1970 is
    719162 days after January 1 of year 1. Euclidean division extends the
    leap-day count to years before 1. -/
def yearStart (year : Int) : Int :=
  let previous := year - 1
  365 * previous + previous / 4 - previous / 100 + previous / 400 - 719162

/-- A civil date candidate with 1-based month and day fields. -/
@[ext]
structure CivilDate where
  year : Int
  month : Nat
  day : Nat
  deriving DecidableEq, Repr

namespace CivilDate

/-- The month is in 1–12 and the day is in 1 through the length of that month. -/
def Valid (date : CivilDate) : Prop :=
  1 ≤ date.month ∧ date.month ≤ 12 ∧ 1 ≤ date.day ∧
    date.day ≤ daysInMonth date.year date.month

instance (date : CivilDate) : Decidable date.Valid :=
  inferInstanceAs (Decidable (1 ≤ date.month ∧ date.month ≤ 12 ∧ 1 ≤ date.day ∧
    date.day ≤ daysInMonth date.year date.month))

/-- Check the fields before interpreting them as a Gregorian date. -/
def valid (date : CivilDate) : Bool := decide date.Valid

end CivilDate

namespace Internal

/-- The zero-based offset of a month start within a year. Index 12 is the
    end of the year and serves as the upper bound for month lookup. -/
def monthStart (leap : Bool) (index : Nat) : Int :=
  if h : index < 12 then
    let month : Std.Time.Month.Ordinal := ⟨(index : Int) + 1, by omega⟩
    (month.cumulativeDays leap).toInt
  else if leap then 366 else 365

end Internal

namespace CivilDate

open Internal
open Silmaril.Numeric.Ieee754.Bisection (lastLE)

/-- Return the signed epoch day of a valid date. Invalid fields yield `none`. -/
def toEpochDay? (date : CivilDate) : Option Int :=
  if date.Valid then
    some (yearStart date.year + monthStart (isLeapYear date.year) (date.month - 1) + date.day - 1)
  else none

/-- Recover a civil date from any signed epoch day. Split into 400-year eras
    starting at year 1, then locate the year and month by their first days. -/
def ofEpochDay (day : Int) : CivilDate :=
  let era := (day - yearStart 1) / 146097
  let firstYear := 1 + 400 * era
  let year := firstYear + lastLE (fun index => yearStart (firstYear + index)) day 0 400
  let dayOfYear := day - yearStart year
  let leap := isLeapYear year
  let monthIndex := lastLE (monthStart leap) dayOfYear 0 12
  ⟨year, monthIndex + 1, (dayOfYear - monthStart leap monthIndex + 1).toNat⟩

end CivilDate

end Silmaril.Numeric.Gregorian
