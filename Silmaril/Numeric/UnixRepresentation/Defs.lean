module

public import Silmaril.Numeric.Timestamp.Defs
public import Silmaril.Numeric.Gregorian.Defs

/-! Integer and civil representations of ideal epoch-relative timestamps. -/

@[expose] public section

namespace Silmaril.Numeric.UnixRepresentation

open Timestamp Gregorian

/-- Select how a fractional destination tick is handled before a range check. -/
inductive TickRounding where
  | exact
  | floor
  | trunc
  deriving DecidableEq, Repr

/-- Convert unbounded ticks on the same epoch scale. Only exact conversion can
    fail. Floor goes toward negative infinity, and truncation goes toward zero. -/
def quantize {kind : Kind} {source : TickUnit} (value : Ticks kind source)
    (target : TickUnit) (rounding : TickRounding) : Option (Ticks kind target) :=
  match rounding with
  | .exact => value.rescale target
  | .floor => some ⟨value.denote.ticks / target.nanosecondsPerTick⟩
  | .trunc => some ⟨value.denote.ticks.tdiv target.nanosecondsPerTick⟩

/-- Fixed-width payloads with their signedness supplied explicitly. -/
inductive WordFormat where
  | int32
  | int64
  | uint64
  deriving DecidableEq, Repr

namespace WordFormat

abbrev Payload : WordFormat → Type
  | .int32 => Int32
  | .int64 => Int64
  | .uint64 => UInt64

def min : WordFormat → Int
  | .int32 => Int32.minValue.toInt
  | .int64 => Int64.minValue.toInt
  | .uint64 => 0

def max : WordFormat → Int
  | .int32 => Int32.maxValue.toInt
  | .int64 => Int64.maxValue.toInt
  | .uint64 => UInt64.size - 1

def toInt : (format : WordFormat) → format.Payload → Int
  | .int32, payload => payload.toInt
  | .int64, payload => payload.toInt
  | .uint64, payload => payload.toNat

/-- The destination tick count fits in the payload's closed integer interval. -/
def InRange (format : WordFormat) (count : Int) : Prop :=
  format.min ≤ count ∧ count ≤ format.max

instance (format : WordFormat) (count : Int) : Decidable (format.InRange count) :=
  inferInstanceAs (Decidable (format.min ≤ count ∧ count ≤ format.max))

def ofInt : (format : WordFormat) → (count : Int) → format.InRange count → format.Payload
  | .int32, count, h => Int32.ofIntLE count h.1 h.2
  | .int64, count, h => Int64.ofIntLE count h.1 h.2
  | .uint64, count, h => UInt64.ofNatLT count.toNat (by
    change 0 ≤ count ∧ count ≤ (UInt64.size : Int) - 1 at h
    omega)

/-- Interpret a word as an exact tick count in the supplied kind and unit. -/
def decode (format : WordFormat) (kind : Kind) (unit : TickUnit) (payload : format.Payload) :
    Ticks kind unit :=
  ⟨format.toInt payload⟩

/-- Quantize first, then check the range of the destination word. -/
def encode (format : WordFormat) {kind : Kind} {source : TickUnit} (value : Ticks kind source)
    (target : TickUnit) (rounding : TickRounding := .exact) : Except ConversionError format.Payload :=
  match quantize value target rounding with
  | none => .error .precisionLoss
  | some count =>
    if h : format.InRange count.ticks then .ok (format.ofInt count.ticks h)
    else .error .outOfRange

end WordFormat

/-- A floor seconds count and a subsecond offset in [0, 10^9), with unbounded seconds. -/
@[ext]
structure Timespec (kind : Kind) where
  seconds : Int
  nanoseconds : Fin 1000000000
  deriving DecidableEq, Repr

namespace Timespec

variable {kind : Kind}

def toTicks (value : Timespec kind) : Ticks kind .nanosecond :=
  ⟨value.seconds * 1000000000 + value.nanoseconds.val⟩

/-- Split with Euclidean division. For example, −1 ns is (−1 s, 999999999 ns). -/
def ofTicks {unit : TickUnit} (value : Ticks kind unit) : Timespec kind :=
  let nanos := value.denote.ticks
  ⟨nanos / 1000000000, ⟨(nanos % 1000000000).toNat, by omega⟩⟩

end Timespec

/-- Civil fields on a uniform 86400-second day scale, using the Gregorian calendar. -/
@[ext]
structure CivilTime where
  date : CivilDate
  hour : Nat
  minute : Nat
  second : Nat
  nanosecond : Fin 1000000000
  deriving DecidableEq, Repr

namespace CivilTime

/-- Encode civil fields, rejecting invalid dates and clock fields outside 00:00:00–23:59:59. -/
def toTimespec? (kind : Kind) (value : CivilTime) : Option (Timespec kind) :=
  match value.date.toEpochDay? with
  | none => none
  | some day =>
    if value.hour < 24 ∧ value.minute < 60 ∧ value.second < 60 then
      some ⟨day * 86400 + (value.hour : Int) * 3600 + (value.minute : Int) * 60 + value.second,
        value.nanosecond⟩
    else none

/-- Decode on the same uniform day scale, with a nonnegative time of day. -/
def ofTimespec {kind : Kind} (value : Timespec kind) : CivilTime :=
  let time := value.seconds % 86400
  ⟨CivilDate.ofEpochDay (value.seconds / 86400), (time / 3600).toNat,
    (time / 60 % 60).toNat, (time % 60).toNat, value.nanoseconds⟩

/-- Encode to exact nanosecond ticks on the caller's epoch scale. -/
def toTicks? (kind : Kind) (value : CivilTime) : Option (Ticks kind .nanosecond) :=
  (value.toTimespec? kind).map Timespec.toTicks

/-- Read civil fields from exact ticks in any supported unit. -/
def ofTicks {kind : Kind} {unit : TickUnit} (value : Ticks kind unit) : CivilTime :=
  ofTimespec (Timespec.ofTicks value)

end CivilTime

end Silmaril.Numeric.UnixRepresentation
