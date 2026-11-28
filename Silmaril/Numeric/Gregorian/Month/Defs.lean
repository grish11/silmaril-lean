module

public import Silmaril.Numeric.Gregorian.Defs

/-! # Gregorian months as half-open signed epoch-day intervals -/

@[expose] public section

namespace Silmaril.Numeric.Gregorian

/-- A proleptic Gregorian month candidate. The year uses astronomical numbering. -/
@[ext] structure CivilMonth where
  year : Int
  month : Nat
  deriving DecidableEq, Repr

/-- A half-open interval of signed days relative to 1970-01-01. -/
structure MonthInterval where
  start : Int
  stop : Int
  deriving DecidableEq, Repr

def MonthInterval.Contains (bounds : MonthInterval) (day : Int) : Prop :=
  bounds.start ≤ day ∧ day < bounds.stop

namespace CivilMonth

def Valid (value : CivilMonth) : Prop :=
  1 ≤ value.month ∧ value.month ≤ 12

instance (value : CivilMonth) : Decidable value.Valid :=
  inferInstanceAs (Decidable (1 ≤ value.month ∧ value.month ≤ 12))

def firstDay (value : CivilMonth) : CivilDate :=
  ⟨value.year, value.month, 1⟩

/-- The successor of a valid month, with December advancing the year. -/
def next (value : CivilMonth) : CivilMonth :=
  if value.month = 12 then ⟨value.year + 1, 1⟩ else ⟨value.year, value.month + 1⟩

/-- Validate the first day, then use the Gregorian month length for the exclusive bound. -/
def interval? (value : CivilMonth) : Option MonthInterval :=
  value.firstDay.toEpochDay?.map fun start => ⟨start, start + daysInMonth value.year value.month⟩

/-- Every signed day has a Gregorian month. -/
def ofEpochDay (day : Int) : CivilMonth :=
  let date := CivilDate.ofEpochDay day
  ⟨date.year, date.month⟩

end CivilMonth

end Silmaril.Numeric.Gregorian
