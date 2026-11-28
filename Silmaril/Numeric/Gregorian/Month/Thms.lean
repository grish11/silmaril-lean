module

public import Silmaril.Numeric.Gregorian.Month.Defs
import Silmaril.Numeric.Gregorian.Thms
import Silmaril.Proofs.Numeric.Gregorian.Month

public section

namespace Silmaril.Numeric.Gregorian.CivilMonth

/-- The first day is valid exactly when the month number is valid. -/
theorem firstDay_valid_iff {value : CivilMonth} : value.firstDay.Valid ↔ value.Valid :=
  Proofs.Numeric.Gregorian.Month.firstDay_valid_iff

theorem next_valid {value : CivilMonth} (valid : value.Valid) : value.next.Valid :=
  Proofs.Numeric.Gregorian.Month.next_valid valid

/-- The checked interval starts on day one and has the Gregorian month length. -/
theorem interval?_eq_some_iff {value : CivilMonth} {bounds : MonthInterval} :
    value.interval? = some bounds ↔
      value.firstDay.toEpochDay? = some bounds.start ∧
      bounds.stop = bounds.start + daysInMonth value.year value.month :=
  Proofs.Numeric.Gregorian.Month.interval?_eq_some_iff

theorem interval?_isSome_iff (value : CivilMonth) :
    value.interval?.isSome = true ↔ value.Valid :=
  Proofs.Numeric.Gregorian.Month.interval?_isSome_iff value

theorem interval_length {value : CivilMonth} {bounds : MonthInterval}
    (checked : value.interval? = some bounds) :
    bounds.stop - bounds.start = daysInMonth value.year value.month := by
  have width := (interval?_eq_some_iff.mp checked).2
  omega

/-- Each signed day projects to a valid Gregorian month. -/
theorem ofEpochDay_valid (day : Int) : (CivilMonth.ofEpochDay day).Valid :=
  let valid := CivilDate.ofEpochDay_valid day
  ⟨valid.1, valid.2.1⟩

/-- Membership selects exactly the Gregorian month of the decoded day. -/
theorem contains_iff {value : CivilMonth} {bounds : MonthInterval} {day : Int}
    (checked : value.interval? = some bounds) :
    bounds.Contains day ↔ CivilMonth.ofEpochDay day = value :=
  Proofs.Numeric.Gregorian.Month.contains_iff checked

/-- A month's exclusive bound is its successor's inclusive bound, also in December. -/
theorem interval_next {value : CivilMonth} {bounds : MonthInterval}
    (checked : value.interval? = some bounds) :
    ∃ nextBounds, value.next.interval? = some nextBounds ∧ bounds.stop = nextBounds.start :=
  Proofs.Numeric.Gregorian.Month.interval_next checked

end Silmaril.Numeric.Gregorian.CivilMonth
