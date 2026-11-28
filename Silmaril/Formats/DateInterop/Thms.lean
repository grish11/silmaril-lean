module

public import Silmaril.Formats.DateInterop.Defs
import Silmaril.Proofs.Formats.DateInterop.Scalar

/-! Exact signed date payload domains and Gregorian round trips. -/

public section

namespace Silmaril.Formats.DateInterop

open Silmaril.Numeric.Gregorian (CivilDate)

namespace Date32

theorem ofEpochDay?_eq_some_iff {day : Int} {value : Payload} :
    ofEpochDay? day = some value ↔ toEpochDay value = day :=
  Proofs.Formats.DateInterop.date32_ofEpochDay?_eq_some_iff

/-- Every signed Int32 day count is representable, including both endpoints. -/
theorem ofEpochDay?_isSome_iff (day : Int) :
    (ofEpochDay? day).isSome = true ↔ -2147483648 ≤ day ∧ day ≤ 2147483647 :=
  Proofs.Formats.DateInterop.date32_ofEpochDay?_isSome_iff day

theorem ofCivil?_eq_some_iff {date : CivilDate} {value : Payload} :
    ofCivil? date = some value ↔ toCivil value = date :=
  Proofs.Formats.DateInterop.date32_ofCivil?_eq_some_iff

@[simp] theorem ofCivil?_toCivil (value : Payload) : ofCivil? (toCivil value) = some value :=
  ofCivil?_eq_some_iff.mpr rfl

theorem toCivil_ofCivil? {date : CivilDate} {value : Payload} (h : ofCivil? date = some value) :
    toCivil value = date :=
  ofCivil?_eq_some_iff.mp h

end Date32

namespace Date64

theorem ofEpochDay?_eq_some_iff {day : Int} {value : Payload} :
    ofEpochDay? day = some value ↔ value.toInt = day * millisecondsPerDay :=
  Proofs.Formats.DateInterop.date64_ofEpochDay?_eq_some_iff

theorem toEpochDay?_eq_some_iff {day : Int} {value : Payload} :
    toEpochDay? value = some day ↔ value.toInt = day * millisecondsPerDay :=
  Proofs.Formats.DateInterop.date64_toEpochDay?_eq_some_iff

/-- A fractional day in either direction is rejected without rounding. -/
theorem toEpochDay?_eq_none_iff (value : Payload) :
    toEpochDay? value = none ↔ value.toInt % millisecondsPerDay ≠ 0 := by
  by_cases whole : value.toInt % millisecondsPerDay = 0 <;> simp [toEpochDay?, whole]

/-- These are the tight whole-day endpoints within signed Int64 milliseconds. -/
theorem ofEpochDay?_isSome_iff (day : Int) :
    (ofEpochDay? day).isSome = true ↔ -106751991167 ≤ day ∧ day ≤ 106751991167 :=
  Proofs.Formats.DateInterop.date64_ofEpochDay?_isSome_iff day

/-- A valid encoding and an exact whole-day decoding are inverse relations. -/
theorem ofCivil?_eq_some_iff {date : CivilDate} {value : Payload} :
    ofCivil? date = some value ↔ toCivil? value = some date :=
  Proofs.Formats.DateInterop.date64_ofCivil?_eq_some_iff

theorem ofCivil?_toCivil? {date : CivilDate} {value : Payload} (h : toCivil? value = some date) :
    ofCivil? date = some value :=
  ofCivil?_eq_some_iff.mpr h

theorem toCivil?_ofCivil? {date : CivilDate} {value : Payload} (h : ofCivil? date = some value) :
    toCivil? value = some date :=
  ofCivil?_eq_some_iff.mp h

end Date64

namespace ParquetDate

theorem ofEpochDay?_eq_some_iff {day : Int} {value : Payload} :
    ofEpochDay? day = some value ↔ toEpochDay value = day :=
  Date32.ofEpochDay?_eq_some_iff

theorem ofEpochDay?_isSome_iff (day : Int) :
    (ofEpochDay? day).isSome = true ↔ -2147483648 ≤ day ∧ day ≤ 2147483647 :=
  Date32.ofEpochDay?_isSome_iff day

theorem ofCivil?_eq_some_iff {date : CivilDate} {value : Payload} :
    ofCivil? date = some value ↔ toCivil value = date :=
  Date32.ofCivil?_eq_some_iff

@[simp] theorem ofCivil?_toCivil (value : Payload) : ofCivil? (toCivil value) = some value :=
  Date32.ofCivil?_toCivil value

theorem toCivil_ofCivil? {date : CivilDate} {value : Payload} (h : ofCivil? date = some value) :
    toCivil value = date :=
  Date32.toCivil_ofCivil? h

end ParquetDate

end Silmaril.Formats.DateInterop
