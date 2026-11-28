module

public import Silmaril.Formats.Parquet.Int96.Defs
import Silmaril.Numeric.Timestamp.Thms
import Silmaril.Proofs.Formats.Parquet.Int96.Wire
import Silmaril.Proofs.Formats.Parquet.Int96.Time

public section

namespace Silmaril.Formats.Parquet.Int96.Payload

open Silmaril.Numeric.Timestamp

@[simp] theorem encode_length (value : Payload) : value.encode.length = 12 :=
  Proofs.Formats.Parquet.Int96.encode_length value

@[simp] theorem decode_encode (value : Payload) : decode? value.encode = some value :=
  Proofs.Formats.Parquet.Int96.decode_encode value

/-- Every accepted payload reproduces the exact input bytes. -/
theorem encode_of_decode {bytes : List UInt8} {value : Payload}
    (h : decode? bytes = some value) : value.encode = bytes :=
  Proofs.Formats.Parquet.Int96.encode_of_decode h

theorem decode_eq_none_iff (bytes : List UInt8) : decode? bytes = none ↔
    bytes.length ≠ 12 ∨ nanosecondsPerDay ≤ KBytes.leVal (bytes.take 8) :=
  Proofs.Formats.Parquet.Int96.decode_eq_none_iff bytes

/-- Successful construction recovers precisely the requested day and subday. -/
theorem ofEpochDay_eq_some_iff {day : Int} {time : Fin nanosecondsPerDay} {value : Payload} :
    ofEpochDay? day time = some value ↔ day = value.epochDay ∧ time = value.nanosecondOfDay :=
  Proofs.Formats.Parquet.Int96.ofEpochDay_eq_some_iff

theorem ofTicks_eq_none_iff (policy : Policy) {unit : TickUnit} (value : Ticks policy.kind unit) :
    let julian := value.denote.ticks / nanosecondsPerDay + unixEpochJulianDay
    ofTicks? policy value = none ↔
      ¬ (Int32.minValue.toInt ≤ julian ∧ julian ≤ Int32.maxValue.toInt) :=
  Proofs.Formats.Parquet.Int96.ofTicks_eq_none_iff policy value

/-- Successful encoding preserves the exact nanosecond denotation. -/
theorem toTicks_ofTicks {policy : Policy} {unit : TickUnit} {ticks : Ticks policy.kind unit}
    {value : Payload} (h : ofTicks? policy ticks = some value) : value.toTicks policy = ticks.denote :=
  Proofs.Formats.Parquet.Int96.toTicks_ofTicks h

@[simp] theorem ofTicks_toTicks (value : Payload) (policy : Policy) :
    ofTicks? policy (value.toTicks policy) = some value :=
  Proofs.Formats.Parquet.Int96.ofTicks_toTicks value policy

/-- Successful narrowing to another precision preserves the exact nanosecond coordinate. -/
theorem toInt64_eq_ok_iff (value : Payload) (policy : Policy) (target : TickUnit) {output : Int64} :
    value.toInt64 policy target = .ok output ↔
      value.toTicks policy = (Ticks.ofInt64 policy.kind target output).denote := by
  have scaleOne : (value.toTicks policy).denote = value.toTicks policy :=
    congrArg Ticks.mk (Int.mul_one _)
  rw [toInt64, Ticks.toInt64_eq_ok_iff, scaleOne]

@[simp] theorem ofGregorian_toGregorian (value : Payload) :
    ofGregorian? value.toGregorian = some value :=
  Proofs.Formats.Parquet.Int96.ofGregorian_toGregorian value

theorem toGregorian_ofGregorian {civil : CivilTime} {value : Payload}
    (h : ofGregorian? civil = some value) : value.toGregorian = civil :=
  Proofs.Formats.Parquet.Int96.toGregorian_ofGregorian h

end Silmaril.Formats.Parquet.Int96.Payload
