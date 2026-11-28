module

public import Silmaril.Formats.DateInterop.Conversion.Defs
import Silmaril.Proofs.Formats.DateInterop.Conversion
import Silmaril.Numeric.Gregorian.Thms

public section

namespace Silmaril.Formats.DateInterop

/-- Widening retains the signed day as exactly 86,400,000 milliseconds per day. -/
theorem Date32.widen_toInt (value : Date32.Payload) :
    (Date32.widen value).toInt = value.toInt * Date64.millisecondsPerDay :=
  Proofs.Formats.DateInterop.Conversion.widen_toInt value

theorem Date64.narrow?_eq_some_iff {source : Date64.Payload} {target : Date32.Payload} :
    Date64.narrow? source = some target ↔
      source.toInt = target.toInt * Date64.millisecondsPerDay :=
  Proofs.Formats.DateInterop.Conversion.narrow?_eq_some_iff

/-- Admission requires an exact whole day in the signed Int32 range. -/
theorem Date64.narrow?_isSome_iff (value : Date64.Payload) :
    (Date64.narrow? value).isSome = true ↔
      ∃ day, value.toInt = day * Date64.millisecondsPerDay ∧
        -2147483648 ≤ day ∧ day ≤ 2147483647 :=
  Proofs.Formats.DateInterop.Conversion.narrow?_isSome_iff value

@[simp] theorem Date64.narrow?_widen (value : Date32.Payload) :
    Date64.narrow? (Date32.widen value) = some value :=
  Date64.narrow?_eq_some_iff.mpr (Date32.widen_toInt value)

theorem Date32.widen_of_narrow? {source : Date64.Payload} {target : Date32.Payload}
    (narrowed : Date64.narrow? source = some target) : Date32.widen target = source :=
  Int64.toInt.inj ((Date32.widen_toInt target).trans (Date64.narrow?_eq_some_iff.mp narrowed).symm)

/-- The scalar conversion can also use the checked civil-date observation. -/
theorem Date64.narrow?_eq_civil (value : Date64.Payload) :
    Date64.narrow? value = (Date64.toCivil? value).bind Date32.ofCivil? := by
  cases day : Date64.toEpochDay? value <;>
    simp [Date64.narrow?, Date64.toCivil?, day, Date32.ofCivil?,
      Numeric.Gregorian.CivilDate.toEpochDay?_ofEpochDay]

end Silmaril.Formats.DateInterop
