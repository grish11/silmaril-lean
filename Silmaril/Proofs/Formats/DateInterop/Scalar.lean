module

public import Silmaril.Formats.DateInterop.Defs
import Silmaril.Numeric.Gregorian.Thms
import Silmaril.Numeric.UnixRepresentation.Thms

public section

namespace Silmaril.Proofs.Formats.DateInterop

open Silmaril.Formats.DateInterop
open Silmaril.Formats.DateInterop.Internal (checked)
open Silmaril.Numeric.Gregorian (CivilDate)
open Silmaril.Numeric.UnixRepresentation (WordFormat)

private theorem checked_eq_some_iff {format : WordFormat} (injective : Function.Injective format.toInt)
    {count : Int} {value : format.Payload} :
    checked format count = some value ↔ format.toInt value = count := by
  unfold checked
  split
  next inRange =>
    rw [Option.some.injEq]
    constructor
    · rintro rfl
      exact WordFormat.toInt_ofInt inRange
    · intro equal
      exact injective ((WordFormat.toInt_ofInt inRange).trans equal.symm)
  next outside =>
    constructor
    · intro impossible
      cases impossible
    · rintro rfl
      exact (outside (WordFormat.toInt_inRange value)).elim

private theorem checked_isSome_iff (format : WordFormat) (count : Int) :
    (checked format count).isSome = true ↔ format.InRange count := by
  by_cases inRange : format.InRange count <;> simp [checked, inRange]

theorem date32_ofEpochDay?_eq_some_iff {day : Int} {value : Date32.Payload} :
    Date32.ofEpochDay? day = some value ↔ Date32.toEpochDay value = day :=
  checked_eq_some_iff (format := .int32) (by intro a b equal; exact Int32.toInt.inj equal)

theorem date32_ofEpochDay?_isSome_iff (day : Int) :
    (Date32.ofEpochDay? day).isSome = true ↔ -2147483648 ≤ day ∧ day ≤ 2147483647 :=
  checked_isSome_iff .int32 day

theorem date32_ofCivil?_eq_some_iff {date : CivilDate} {value : Date32.Payload} :
    Date32.ofCivil? date = some value ↔ Date32.toCivil value = date := by
  constructor
  · intro encoded
    cases day : date.toEpochDay? with
    | none => simp [Date32.ofCivil?, day] at encoded
    | some count =>
      have signed := date32_ofEpochDay?_eq_some_iff.mp (by simpa [Date32.ofCivil?, day] using encoded)
      exact (congrArg CivilDate.ofEpochDay signed).trans (CivilDate.ofEpochDay_toEpochDay? day)
  · rintro rfl
    simp [Date32.ofCivil?, Date32.toCivil, CivilDate.toEpochDay?_ofEpochDay, date32_ofEpochDay?_eq_some_iff]

theorem date64_ofEpochDay?_eq_some_iff {day : Int} {value : Date64.Payload} :
    Date64.ofEpochDay? day = some value ↔ value.toInt = day * Date64.millisecondsPerDay :=
  checked_eq_some_iff (format := .int64) (by intro a b equal; exact Int64.toInt.inj equal)

theorem date64_toEpochDay?_eq_some_iff {day : Int} {value : Date64.Payload} :
    Date64.toEpochDay? value = some day ↔ value.toInt = day * Date64.millisecondsPerDay := by
  unfold Date64.toEpochDay? Date64.millisecondsPerDay
  split <;> simp_all <;> omega

theorem date64_ofEpochDay?_isSome_iff (day : Int) :
    (Date64.ofEpochDay? day).isSome = true ↔ -106751991167 ≤ day ∧ day ≤ 106751991167 := by
  rw [Date64.ofEpochDay?, checked_isSome_iff]
  change -9223372036854775808 ≤ day * 86400000 ∧ day * 86400000 ≤ 9223372036854775807 ↔ _
  omega

theorem date64_ofCivil?_eq_some_iff {date : CivilDate} {value : Date64.Payload} :
    Date64.ofCivil? date = some value ↔ Date64.toCivil? value = some date := by
  constructor
  · intro encoded
    cases day : date.toEpochDay? with
    | none => simp [Date64.ofCivil?, day] at encoded
    | some count =>
      have ticks := date64_ofEpochDay?_eq_some_iff.mp (by simpa [Date64.ofCivil?, day] using encoded)
      have decoded := date64_toEpochDay?_eq_some_iff.mpr ticks
      simp [Date64.toCivil?, decoded, CivilDate.ofEpochDay_toEpochDay? day]
  · intro decoded
    cases day : Date64.toEpochDay? value with
    | none => simp [Date64.toCivil?, day] at decoded
    | some count =>
      have civil : CivilDate.ofEpochDay count = date := by simpa [Date64.toCivil?, day] using decoded
      subst date
      simp [Date64.ofCivil?, CivilDate.toEpochDay?_ofEpochDay, date64_ofEpochDay?_eq_some_iff,
        date64_toEpochDay?_eq_some_iff.mp day]

end Silmaril.Proofs.Formats.DateInterop
