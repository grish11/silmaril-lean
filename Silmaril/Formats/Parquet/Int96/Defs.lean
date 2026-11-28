module

public import Silmaril.Numeric.Gregorian.Defs
public import Silmaril.Numeric.Timestamp.Defs
public import Silmaril.Prelude.Bytes.Digits.Defs

/-! # Legacy Parquet INT96 timestamp payloads -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Int96

open Silmaril.Numeric.Timestamp
open Silmaril.Numeric.Gregorian (CivilDate)

/-- The interpretation is supplied from outside the payload. Both policies
    use proleptic Gregorian dates and uniform 86,400-second days. -/
inductive Policy where
  | prolepticUtc
  | prolepticLocal

def Policy.kind : Policy → Kind
  | .prolepticUtc => .utcInstant
  | .prolepticLocal => .localReading

def nanosecondsPerDay : Nat := 86400000000000

def unixEpochJulianDay : Int := 2440588

/-- A signed Julian day field and a nonnegative nanosecond count below one day. -/
structure Payload where
  julianDay : Int32
  nanosecondOfDay : Fin nanosecondsPerDay
  deriving DecidableEq, Repr

namespace Payload

/-- Eight little-endian time-of-day bytes followed by four little-endian day bytes. -/
def encode (value : Payload) : List UInt8 :=
  KBytes.unpack 8 value.nanosecondOfDay.val ++ KBytes.unpack 4 value.julianDay.toUInt32.toNat

/-- Read exactly one payload. Reject a negative or oversized time-of-day word. -/
def decode? (bytes : List UInt8) : Option Payload :=
  if bytes.length = 12 then
    let nanos := KBytes.leVal (bytes.take 8)
    if h : nanos < nanosecondsPerDay then
      some ⟨(UInt32.ofNat (KBytes.leVal (bytes.drop 8))).toInt32, ⟨nanos, h⟩⟩
    else none
  else none

def epochDay (value : Payload) : Int :=
  value.julianDay.toInt - unixEpochJulianDay

/-- Validate the shifted day before narrowing to the signed wire field. -/
def ofEpochDay? (day : Int) (time : Fin nanosecondsPerDay) : Option Payload :=
  let julian := day + unixEpochJulianDay
  if h : Int32.minValue.toInt ≤ julian ∧ julian ≤ Int32.maxValue.toInt then
    some ⟨Int32.ofIntLE julian h.1 h.2, time⟩
  else none

/-- Interpret the same bits on the epoch scale selected by the caller. -/
def toTicks (value : Payload) (policy : Policy) : Ticks policy.kind .nanosecond :=
  ⟨value.epochDay * nanosecondsPerDay + value.nanosecondOfDay.val⟩

/-- Use Euclidean division so negative offsets still have a nonnegative time of day. -/
def ofTicks? (policy : Policy) {unit : TickUnit} (value : Ticks policy.kind unit) : Option Payload :=
  let nanos := value.denote.ticks
  ofEpochDay? (nanos / nanosecondsPerDay) ⟨(nanos % nanosecondsPerDay).toNat,
    (Int.toNat_lt' (by decide : 0 < nanosecondsPerDay)).mpr (Int.emod_lt_of_pos nanos (by decide))⟩

/-- Checked narrowing to the specified tick unit and signed 64-bit range. -/
def toInt64 (value : Payload) (policy : Policy) (target : TickUnit) : Except ConversionError Int64 :=
  (value.toTicks policy).toInt64 target

end Payload

/-- Proleptic Gregorian coordinates on a uniform day scale. -/
structure CivilTime where
  date : CivilDate
  nanosecondOfDay : Fin nanosecondsPerDay
  deriving DecidableEq, Repr

def Payload.toGregorian (value : Payload) : CivilTime :=
  ⟨CivilDate.ofEpochDay value.epochDay, value.nanosecondOfDay⟩

/-- Check the date and the signed wire day range. -/
def Payload.ofGregorian? (value : CivilTime) : Option Payload := do
  let day ← value.date.toEpochDay?
  ofEpochDay? day value.nanosecondOfDay

end Silmaril.Formats.Parquet.Int96
