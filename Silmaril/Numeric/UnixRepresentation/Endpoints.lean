module

public import Silmaril.Numeric.UnixRepresentation.Defs
import Silmaril.Proofs.Numeric.UnixRepresentation.Endpoints

/-! Fixed-width Unix limits expressed as Gregorian civil times. -/

public section

namespace Silmaril.Numeric.UnixRepresentation

open Timestamp

/-- The earliest signed 32-bit Unix second. -/
theorem int32SecondsMinimum :
    let civil : CivilTime := ⟨⟨1901, 12, 13⟩, 20, 45, 52, 0⟩;
    Int32.minValue.toInt = -2147483648 ∧
      CivilTime.ofTicks (WordFormat.int32.decode .utcInstant .second Int32.minValue) = civil ∧
      (civil.toTicks? .utcInstant).map (fun ticks => WordFormat.int32.encode ticks .second) =
        some (.ok Int32.minValue) :=
  Proofs.Numeric.UnixRepresentation.int32SecondsMinimum

/-- The latest signed 32-bit Unix second. -/
theorem int32SecondsMaximum :
    let civil : CivilTime := ⟨⟨2038, 1, 19⟩, 3, 14, 7, 0⟩;
    Int32.maxValue.toInt = 2147483647 ∧
      CivilTime.ofTicks (WordFormat.int32.decode .utcInstant .second Int32.maxValue) = civil ∧
      (civil.toTicks? .utcInstant).map (fun ticks => WordFormat.int32.encode ticks .second) =
        some (.ok Int32.maxValue) :=
  Proofs.Numeric.UnixRepresentation.int32SecondsMaximum

/-- The next second after the signed 32-bit maximum is exactly on the seconds grid. -/
theorem int32SecondsFirstOverflow :
    let civil : CivilTime := ⟨⟨2038, 1, 19⟩, 3, 14, 8, 0⟩;
    Int32.maxValue.toInt + 1 = 2147483648 ∧
      CivilTime.ofTicks (⟨2147483648⟩ : Ticks .utcInstant .second) = civil ∧
      (civil.toTicks? .utcInstant).bind (fun ticks => ticks.rescale .second) =
        some ⟨2147483648⟩ ∧
      (civil.toTicks? .utcInstant).map (fun ticks => WordFormat.int32.encode ticks .second) =
        some (.error .outOfRange) :=
  Proofs.Numeric.UnixRepresentation.int32SecondsFirstOverflow

/-- The earliest signed 64-bit Unix nanosecond. -/
theorem int64NanosecondsMinimum :
    let civil : CivilTime := ⟨⟨1677, 9, 21⟩, 0, 12, 43, 145224192⟩;
    Int64.minValue.toInt = -9223372036854775808 ∧
      CivilTime.ofTicks (WordFormat.int64.decode .utcInstant .nanosecond Int64.minValue) = civil ∧
      (civil.toTicks? .utcInstant).map (fun ticks => WordFormat.int64.encode ticks .nanosecond) =
        some (.ok Int64.minValue) :=
  Proofs.Numeric.UnixRepresentation.int64NanosecondsMinimum

/-- The latest signed 64-bit Unix nanosecond. -/
theorem int64NanosecondsMaximum :
    let civil : CivilTime := ⟨⟨2262, 4, 11⟩, 23, 47, 16, 854775807⟩;
    Int64.maxValue.toInt = 9223372036854775807 ∧
      CivilTime.ofTicks (WordFormat.int64.decode .utcInstant .nanosecond Int64.maxValue) = civil ∧
      (civil.toTicks? .utcInstant).map (fun ticks => WordFormat.int64.encode ticks .nanosecond) =
        some (.ok Int64.maxValue) :=
  Proofs.Numeric.UnixRepresentation.int64NanosecondsMaximum

end Silmaril.Numeric.UnixRepresentation
