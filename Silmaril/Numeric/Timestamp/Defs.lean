module

/-! Exact epoch-relative timestamp arithmetic shared by columnar formats. -/

@[expose] public section

namespace Silmaril.Numeric.Timestamp

/-- The epoch interpretation, supplied by the caller. -/
inductive Kind where
  /-- An instant measured relative to 1970-01-01 00:00:00 UTC on the Unix timescale. -/
  | utcInstant
  /-- A wall-clock reading relative to local 1970-01-01 00:00:00 on a uniform day scale. -/
  | localReading

/-- The unit of one tick. -/
inductive TickUnit where
  | second | millisecond | microsecond | nanosecond

def TickUnit.nanosecondsPerTick : TickUnit → Int
  | .second => 1000000000
  | .millisecond => 1000000
  | .microsecond => 1000
  | .nanosecond => 1

/-- Unbounded signed ticks relative to the epoch selected by `kind`. -/
structure Ticks (kind : Kind) (unit : TickUnit) where
  ticks : Int
  deriving DecidableEq, Repr

inductive ConversionError where
  | precisionLoss
  | outOfRange
  deriving DecidableEq, Repr

namespace Ticks

variable {kind : Kind} {source : TickUnit}

/-- The exact offset on the same epoch scale, expressed in integer nanoseconds. -/
def denote (value : Ticks kind source) : Ticks kind .nanosecond :=
  ⟨value.ticks * source.nanosecondsPerTick⟩

/-- Exact unit conversion. A fractional destination tick yields `none`. -/
def rescale (value : Ticks kind source) (target : TickUnit) : Option (Ticks kind target) :=
  let nanos := value.denote.ticks
  let scale := target.nanosecondsPerTick
  if nanos % scale = 0 then some ⟨nanos / scale⟩ else none

/-- Interpret a signed payload using a separately supplied kind and unit. -/
def ofInt64 (kind : Kind) (unit : TickUnit) (payload : Int64) : Ticks kind unit :=
  ⟨payload.toInt⟩

/-- Convert exactly to the target unit and check the signed 64-bit payload range.
    Precision is checked before range. -/
def toInt64 (value : Ticks kind source) (target : TickUnit) : Except ConversionError Int64 :=
  match value.rescale target with
  | none => .error .precisionLoss
  | some result =>
    if h : Int64.minValue.toInt ≤ result.ticks ∧ result.ticks ≤ Int64.maxValue.toInt then
      .ok (Int64.ofIntLE result.ticks h.1 h.2)
    else .error .outOfRange

end Ticks

end Silmaril.Numeric.Timestamp
