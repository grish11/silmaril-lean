module

public import Silmaril.Formats.DateInterop.Conversion.Defs
import Silmaril.Formats.DateInterop.Thms

public section

namespace Silmaril.Proofs.Formats.DateInterop.Conversion

open Silmaril.Formats.DateInterop

theorem widen_toInt (value : Date32.Payload) :
    (Date32.widen value).toInt = value.toInt * Date64.millisecondsPerDay := by
  have lower := Int32.le_toInt value
  have upper := Int32.toInt_lt value
  apply Int64.toInt_ofInt_of_le <;> unfold Date32.toEpochDay Date64.millisecondsPerDay <;> omega

theorem narrow?_eq_some_iff {source : Date64.Payload} {target : Date32.Payload} :
    Date64.narrow? source = some target ↔
      source.toInt = target.toInt * Date64.millisecondsPerDay := by
  rw [Date64.narrow?, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨day, whole, narrowed⟩
    have equal := Date32.ofEpochDay?_eq_some_iff.mp narrowed
    exact (Date64.toEpochDay?_eq_some_iff.mp whole).trans
      (congrArg (· * Date64.millisecondsPerDay) equal.symm)
  · intro exactWord
    exact ⟨target.toInt, Date64.toEpochDay?_eq_some_iff.mpr exactWord,
      Date32.ofEpochDay?_eq_some_iff.mpr rfl⟩

theorem narrow?_isSome_iff (value : Date64.Payload) :
    (Date64.narrow? value).isSome = true ↔
      ∃ day, value.toInt = day * Date64.millisecondsPerDay ∧
        -2147483648 ≤ day ∧ day ≤ 2147483647 := by
  constructor
  · intro admitted
    obtain ⟨target, result⟩ := Option.isSome_iff_exists.mp admitted
    exact ⟨target.toInt, narrow?_eq_some_iff.mp result, Int32.le_toInt target,
      by have upper := Int32.toInt_lt target; omega⟩
  · rintro ⟨day, scaled, lower, upper⟩
    have whole := Date64.toEpochDay?_eq_some_iff.mpr scaled
    simpa [Date64.narrow?, whole] using (Date32.ofEpochDay?_isSome_iff day).mpr ⟨lower, upper⟩

end Silmaril.Proofs.Formats.DateInterop.Conversion
