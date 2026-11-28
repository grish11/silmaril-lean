module

public import Silmaril.Formats.ColumnarTimestamp.Defs
import Silmaril.Numeric.Gregorian.Thms

public section

namespace Silmaril.Proofs.Formats.ColumnarTimestamp

open Silmaril.Formats.ColumnarTimestamp
open Silmaril.Numeric.Timestamp
open Silmaril.Numeric.Gregorian (CivilDate)

theorem arrow_kind_eq_utcInstant_iff (metadata : Arrow.Metadata) :
    metadata.kind = .utcInstant ↔ ∃ name, metadata.timezone = some name ∧ name ≠ "" := by
  cases h : metadata.timezone with
  | none => simp [Arrow.Metadata.kind, Arrow.Metadata.timezoneAnnotation, epochKind, h]
  | some name =>
    by_cases empty : name = "" <;>
      simp [Arrow.Metadata.kind, Arrow.Metadata.timezoneAnnotation, epochKind, h, empty]

variable {kind : Kind} {source target : TickUnit}

theorem toInt64_eq_precisionLoss_iff (value : Ticks kind source) :
    value.toInt64 target = .error .precisionLoss ↔
      value.denote.ticks % target.nanosecondsPerTick ≠ 0 := by
  by_cases exactTick : value.denote.ticks % target.nanosecondsPerTick = 0
  · simp [Ticks.toInt64, Ticks.rescale, exactTick]
    split <;> simp
  · simp [Ticks.toInt64, Ticks.rescale, exactTick]

theorem toInt64_eq_outOfRange_iff (value : Ticks kind source) :
    let nanos := value.denote.ticks
    let scale := target.nanosecondsPerTick
    value.toInt64 target = .error .outOfRange ↔ nanos % scale = 0 ∧
      ¬ (Int64.minValue.toInt ≤ nanos / scale ∧ nanos / scale ≤ Int64.maxValue.toInt) := by
  by_cases exactTick : value.denote.ticks % target.nanosecondsPerTick = 0 <;>
    simp [Ticks.toInt64, Ticks.rescale, exactTick]

theorem local_toTicks?_ofTicks {unit : TickUnit} (value : Ticks .localReading unit) :
    (LocalDateTime.ofTicks value).toTicks? = some value.denote := by
  have nonnegative := Int.emod_nonneg value.denote.ticks
    (show (nanosecondsPerDay : Int) ≠ 0 by decide)
  have sameTicks := Int.ediv_mul_add_emod value.denote.ticks (nanosecondsPerDay : Int)
  simp [LocalDateTime.ofTicks, LocalDateTime.toTicks?, CivilDate.toEpochDay?_ofEpochDay,
    Int.toNat_of_nonneg nonnegative, sameTicks]

theorem local_ofTicks_toTicks? {value : LocalDateTime} {ticks : Ticks .localReading .nanosecond}
    (h : value.toTicks? = some ticks) : LocalDateTime.ofTicks ticks = value := by
  cases value with
  | mk date time =>
    cases hd : date.toEpochDay? with
    | none => simp [LocalDateTime.toTicks?, hd] at h
    | some day =>
      simp [LocalDateTime.toTicks?, hd] at h
      subst ticks
      have split := (Int.ediv_emod_unique
        (a := day * nanosecondsPerDay + time.val) (b := nanosecondsPerDay)
        (q := day) (r := time.val) (by decide)).mpr
        ⟨by rw [Int.mul_comm, Int.add_comm], Int.natCast_nonneg _, Int.ofNat_lt.mpr time.isLt⟩
      simp [LocalDateTime.ofTicks, Ticks.denote, TickUnit.nanosecondsPerTick,
        split.1, split.2, CivilDate.ofEpochDay_toEpochDay? hd]

end Silmaril.Proofs.Formats.ColumnarTimestamp
