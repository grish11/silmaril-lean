module

public import Silmaril.Numeric.UnixRepresentation.Defs
import Silmaril.Numeric.UnixRepresentation.Thms
import Silmaril.Numeric.Gregorian.Thms
import Mathlib.Tactic.NormNum
import all Std.Time.Date.Unit.Year
import all Std.Time.Date.Unit.Month
import all Std.Time.Internal.UnitVal

public section

namespace Silmaril.Proofs.Numeric.UnixRepresentation

open Silmaril.Numeric.Timestamp
open Silmaril.Numeric.UnixRepresentation
open Silmaril.Numeric.Gregorian

private theorem endpoint {format : WordFormat} {unit : TickUnit} {payload : format.Payload}
    {civil : CivilTime}
    (encoded : civil.toTicks? .utcInstant = some (format.decode .utcInstant unit payload).denote) :
    CivilTime.ofTicks (format.decode .utcInstant unit payload) = civil ∧
      (civil.toTicks? .utcInstant).map (fun ticks => format.encode ticks unit) =
        some (.ok payload) := by
  refine ⟨CivilTime.ofTicks_toTicks? encoded, ?_⟩
  rw [encoded, Option.map_some]
  apply congrArg some
  exact WordFormat.encode_exact_eq_ok_iff.mpr (by simp [Ticks.denote, TickUnit.nanosecondsPerTick])

theorem int32SecondsMinimum :
    let civil : CivilTime := ⟨⟨1901, 12, 13⟩, 20, 45, 52, 0⟩;
    Int32.minValue.toInt = -2147483648 ∧
      CivilTime.ofTicks (WordFormat.int32.decode .utcInstant .second Int32.minValue) = civil ∧
      (civil.toTicks? .utcInstant).map (fun ticks => WordFormat.int32.encode ticks .second) =
        some (.ok Int32.minValue) := ⟨rfl, endpoint (by
      norm_num [CivilTime.toTicks?, CivilTime.toTimespec?, CivilDate.toEpochDay?, CivilDate.Valid,
        daysInMonth_eq, yearStart, Timespec.toTicks,
        show Internal.monthStart (isLeapYear 1901) 11 = 334 by rfl,
        WordFormat.decode, WordFormat.toInt, Ticks.denote, TickUnit.nanosecondsPerTick])⟩

theorem int32SecondsMaximum :
    let civil : CivilTime := ⟨⟨2038, 1, 19⟩, 3, 14, 7, 0⟩;
    Int32.maxValue.toInt = 2147483647 ∧
      CivilTime.ofTicks (WordFormat.int32.decode .utcInstant .second Int32.maxValue) = civil ∧
      (civil.toTicks? .utcInstant).map (fun ticks => WordFormat.int32.encode ticks .second) =
        some (.ok Int32.maxValue) := ⟨rfl, endpoint (by
      norm_num [CivilTime.toTicks?, CivilTime.toTimespec?, CivilDate.toEpochDay?, CivilDate.Valid,
        daysInMonth_eq, yearStart, Timespec.toTicks, show Int32.maxValue.toInt = 2147483647 by rfl,
        show Internal.monthStart (isLeapYear 2038) 0 = 0 by rfl,
        WordFormat.decode, WordFormat.toInt, Ticks.denote, TickUnit.nanosecondsPerTick])⟩

theorem int32SecondsFirstOverflow :
    let civil : CivilTime := ⟨⟨2038, 1, 19⟩, 3, 14, 8, 0⟩;
    Int32.maxValue.toInt + 1 = 2147483648 ∧
      CivilTime.ofTicks (⟨2147483648⟩ : Ticks .utcInstant .second) = civil ∧
      (civil.toTicks? .utcInstant).bind (fun ticks => ticks.rescale .second) =
        some ⟨2147483648⟩ ∧
      (civil.toTicks? .utcInstant).map (fun ticks => WordFormat.int32.encode ticks .second) =
        some (.error .outOfRange) := by
  dsimp only
  have date : (⟨⟨2038, 1, 19⟩, 3, 14, 8, 0⟩ : CivilTime).toTicks? .utcInstant =
      some (⟨2147483648000000000⟩ : Ticks .utcInstant .nanosecond) := by
    norm_num [CivilTime.toTicks?, CivilTime.toTimespec?, CivilDate.toEpochDay?, CivilDate.Valid,
      daysInMonth_eq, yearStart, Timespec.toTicks,
      show Internal.monthStart (isLeapYear 2038) 0 = 0 by rfl]
  refine ⟨rfl, CivilTime.ofTicks_toTicks? date, ?_, ?_⟩
  · rw [date]
    rfl
  · rw [date, Option.map_some]
    apply congrArg some
    exact WordFormat.encode_eq_outOfRange_iff.mpr ⟨⟨2147483648⟩, rfl, by decide⟩

theorem int64NanosecondsMinimum :
    let civil : CivilTime := ⟨⟨1677, 9, 21⟩, 0, 12, 43, 145224192⟩;
    Int64.minValue.toInt = -9223372036854775808 ∧
      CivilTime.ofTicks (WordFormat.int64.decode .utcInstant .nanosecond Int64.minValue) = civil ∧
      (civil.toTicks? .utcInstant).map (fun ticks => WordFormat.int64.encode ticks .nanosecond) =
        some (.ok Int64.minValue) := ⟨rfl, endpoint (by
      norm_num [CivilTime.toTicks?, CivilTime.toTimespec?, CivilDate.toEpochDay?, CivilDate.Valid,
        daysInMonth_eq, yearStart, Timespec.toTicks,
        show ((145224192 : Fin 1000000000).val : Int) = 145224192 by rfl,
        show Internal.monthStart (isLeapYear 1677) 8 = 243 by rfl,
        WordFormat.decode, WordFormat.toInt, Ticks.denote, TickUnit.nanosecondsPerTick])⟩

theorem int64NanosecondsMaximum :
    let civil : CivilTime := ⟨⟨2262, 4, 11⟩, 23, 47, 16, 854775807⟩;
    Int64.maxValue.toInt = 9223372036854775807 ∧
      CivilTime.ofTicks (WordFormat.int64.decode .utcInstant .nanosecond Int64.maxValue) = civil ∧
      (civil.toTicks? .utcInstant).map (fun ticks => WordFormat.int64.encode ticks .nanosecond) =
        some (.ok Int64.maxValue) := ⟨rfl, endpoint (by
      norm_num [CivilTime.toTicks?, CivilTime.toTimespec?, CivilDate.toEpochDay?, CivilDate.Valid,
        daysInMonth_eq, yearStart, Timespec.toTicks,
        show ((854775807 : Fin 1000000000).val : Int) = 854775807 by rfl,
        show Int64.maxValue.toInt = 9223372036854775807 by rfl,
        show Internal.monthStart (isLeapYear 2262) 3 = 90 by rfl,
        WordFormat.decode, WordFormat.toInt, Ticks.denote, TickUnit.nanosecondsPerTick])⟩

end Silmaril.Proofs.Numeric.UnixRepresentation
