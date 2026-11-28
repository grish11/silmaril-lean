module

public import Silmaril.Formats.Parquet.Int96.Defs
import Silmaril.Numeric.Gregorian.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Int96

open Silmaril.Formats.Parquet.Int96
open Silmaril.Numeric.Timestamp
open Silmaril.Numeric.Gregorian (CivilDate)

theorem ofEpochDay_eq_some_iff {day : Int} {time : Fin nanosecondsPerDay} {value : Payload} :
    Payload.ofEpochDay? day time = some value ↔ day = value.epochDay ∧ time = value.nanosecondOfDay := by
  constructor
  · intro h
    unfold Payload.ofEpochDay? at h
    dsimp only at h
    split at h
    next bounds =>
      cases Option.some.inj h
      exact ⟨by simp [Payload.epochDay], rfl⟩
    next => contradiction
  · rintro ⟨rfl, rfl⟩
    have same : value.epochDay + unixEpochJulianDay = value.julianDay.toInt := by
      simp [Payload.epochDay]
    have bounds : Int32.minValue.toInt ≤ value.julianDay.toInt ∧
        value.julianDay.toInt ≤ Int32.maxValue.toInt :=
      ⟨value.julianDay.minValue_le_toInt, value.julianDay.toInt_le⟩
    simp only [Payload.ofEpochDay?, same, dite_eq_left bounds, Int32.ofIntLE_toInt]

theorem ofTicks_eq_none_iff (policy : Policy) {unit : TickUnit} (value : Ticks policy.kind unit) :
    let julian := value.denote.ticks / nanosecondsPerDay + unixEpochJulianDay
    Payload.ofTicks? policy value = none ↔
      ¬ (Int32.minValue.toInt ≤ julian ∧ julian ≤ Int32.maxValue.toInt) := by
  dsimp only [Payload.ofTicks?, Payload.ofEpochDay?]
  split
  next bounds => simp only [reduceCtorEq, bounds, true_and, not_true_eq_false]
  next bounds => simp only [bounds, not_false_eq_true]

theorem toTicks_ofTicks {policy : Policy} {unit : TickUnit} {ticks : Ticks policy.kind unit}
    {value : Payload} (h : Payload.ofTicks? policy ticks = some value) :
    value.toTicks policy = ticks.denote := by
  have coordinates := ofEpochDay_eq_some_iff.mp h
  have nonnegative := Int.emod_nonneg ticks.denote.ticks
    (show (nanosecondsPerDay : Int) ≠ 0 by decide)
  have subday := congrArg Fin.val coordinates.2
  change (ticks.denote.ticks % (nanosecondsPerDay : Int)).toNat = value.nanosecondOfDay.val at subday
  apply congrArg Ticks.mk
  rw [← coordinates.1, ← subday, Int.toNat_of_nonneg nonnegative, Int.ediv_mul_add_emod]
  rfl

theorem ofTicks_toTicks (value : Payload) (policy : Policy) :
    Payload.ofTicks? policy (value.toTicks policy) = some value := by
  apply ofEpochDay_eq_some_iff.mpr
  have split := (Int.ediv_emod_unique
    (a := value.epochDay * nanosecondsPerDay + value.nanosecondOfDay.val)
    (b := nanosecondsPerDay) (q := value.epochDay) (r := value.nanosecondOfDay.val) (by decide)).mpr
    ⟨by rw [Int.mul_comm, Int.add_comm], Int.natCast_nonneg _,
      Int.ofNat_lt.mpr value.nanosecondOfDay.isLt⟩
  refine ⟨?_, Fin.ext ?_⟩ <;>
    simp [Payload.toTicks, Ticks.denote, TickUnit.nanosecondsPerTick, split.1, split.2]

theorem ofGregorian_toGregorian (value : Payload) :
    Payload.ofGregorian? value.toGregorian = some value := by
  simp only [Payload.ofGregorian?, Payload.toGregorian, CivilDate.toEpochDay?_ofEpochDay]
  exact ofEpochDay_eq_some_iff.mpr ⟨rfl, rfl⟩

theorem toGregorian_ofGregorian {civil : CivilTime} {value : Payload}
    (h : Payload.ofGregorian? civil = some value) : value.toGregorian = civil := by
  cases hd : civil.date.toEpochDay? with
  | none => simp [Payload.ofGregorian?, hd] at h
  | some day =>
    simp only [Payload.ofGregorian?, hd] at h
    have coordinates := ofEpochDay_eq_some_iff.mp h
    change CivilTime.mk (CivilDate.ofEpochDay value.epochDay) value.nanosecondOfDay = civil
    rw [← coordinates.1, ← coordinates.2, CivilDate.ofEpochDay_toEpochDay? hd]

end Silmaril.Proofs.Formats.Parquet.Int96
