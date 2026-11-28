module

public import Silmaril.Numeric.Gregorian.Defs

/-! # Ordinal dates and ISO week dates on the Gregorian epoch-day scale -/

@[expose] public section

namespace Silmaril.Numeric.Gregorian

/-- A year and a one-based day within that Gregorian year. -/
structure OrdinalDate where
  year : Int
  ordinal : Nat
  deriving DecidableEq, Repr

namespace OrdinalDate

def Valid (date : OrdinalDate) : Prop := 1 ≤ date.ordinal ∧ date.ordinal ≤ daysInYear date.year

instance (date : OrdinalDate) : Decidable date.Valid :=
  inferInstanceAs (Decidable (1 ≤ date.ordinal ∧ date.ordinal ≤ daysInYear date.year))

def toEpochDay? (date : OrdinalDate) : Option Int :=
  if date.Valid then some (yearStart date.year + date.ordinal - 1) else none

def ofEpochDay (day : Int) : OrdinalDate :=
  let year := (CivilDate.ofEpochDay day).year
  ⟨year, (day - yearStart year + 1).toNat⟩

def toCivil? (date : OrdinalDate) : Option CivilDate := date.toEpochDay?.map CivilDate.ofEpochDay

def ofCivil? (date : CivilDate) : Option OrdinalDate := date.toEpochDay?.map ofEpochDay

end OrdinalDate

/-- Monday of the week containing January 4. Epoch day zero was a Thursday. -/
def weekYearStart (year : Int) : Int :=
  let january4 := yearStart year + 3
  january4 - (january4 + 3) % 7

def weeksInYear (year : Int) : Nat :=
  ((weekYearStart (year + 1) - weekYearStart year) / 7).toNat

/-- An ISO week-year, a one-based week and a weekday with Monday numbered 1. -/
structure WeekDate where
  year : Int
  week : Nat
  weekday : Nat
  deriving DecidableEq, Repr

namespace WeekDate

def Valid (date : WeekDate) : Prop :=
  1 ≤ date.week ∧ date.week ≤ weeksInYear date.year ∧ 1 ≤ date.weekday ∧ date.weekday ≤ 7

instance (date : WeekDate) : Decidable date.Valid :=
  inferInstanceAs (Decidable
    (1 ≤ date.week ∧ date.week ≤ weeksInYear date.year ∧ 1 ≤ date.weekday ∧ date.weekday ≤ 7))

def toEpochDay? (date : WeekDate) : Option Int :=
  if date.Valid then some (weekYearStart date.year + 7 * ((date.week : Int) - 1) + date.weekday - 1)
  else none

/-- A week near a January boundary may belong to the adjacent week-year. -/
def weekYear (day : Int) : Int :=
  let year := (CivilDate.ofEpochDay day).year
  if day < weekYearStart year then year - 1
  else if weekYearStart (year + 1) ≤ day then year + 1
  else year

def ofEpochDay (day : Int) : WeekDate :=
  let year := weekYear day
  let offset := day - weekYearStart year
  ⟨year, (offset / 7 + 1).toNat, (offset % 7 + 1).toNat⟩

def toCivil? (date : WeekDate) : Option CivilDate := date.toEpochDay?.map CivilDate.ofEpochDay

def ofCivil? (date : CivilDate) : Option WeekDate := date.toEpochDay?.map ofEpochDay

end WeekDate

end Silmaril.Numeric.Gregorian
