module

public import Silmaril.Numeric.Gregorian.Defs
public import Silmaril.Numeric.Timestamp.Defs
public import Silmaril.Numeric.DecimalText

/-! # Extended calendar date/time text

The profile uses uppercase RFC 3339 date-time syntax with known offsets and
exact nanosecond precision. See `docs/projects/iso8601-calendar-profile.md`.
-/

@[expose] public section

namespace Silmaril.Formats.ISO8601

open Numeric.Gregorian (CivilDate)
open Numeric.Timestamp (ConversionError Ticks TickUnit)

inductive Error where
  | syntax
  | invalidDate
  | invalidTime
  | fractionPrecision
  | invalidOffset
  | conversion (error : ConversionError)
  deriving DecidableEq, Repr

/-- A validated local reading on a proleptic Gregorian epoch-day scale.
    Every epoch day names a valid date, and the clock fields are bounded. -/
structure LocalDateTime where
  epochDay : Int
  hour : Fin 24
  minute : Fin 60
  second : Fin 60
  nanosecond : Fin 1000000000
  deriving DecidableEq, Repr

namespace LocalDateTime

/-- Validate the calendar date independently of the clock fields. -/
def ofCivil (date : CivilDate) (hour minute second nanosecond : Nat) :
    Except Error LocalDateTime :=
  match date.toEpochDay? with
  | none => .error .invalidDate
  | some day =>
    if h : hour < 24 ∧ minute < 60 ∧ second < 60 ∧ nanosecond < 1000000000 then
      .ok ⟨day, ⟨hour, h.1⟩, ⟨minute, h.2.1⟩, ⟨second, h.2.2.1⟩, ⟨nanosecond, h.2.2.2⟩⟩
    else .error .invalidTime

def date (reading : LocalDateTime) : CivilDate := CivilDate.ofEpochDay reading.epochDay

/-- Interpret the reading relative to local midnight on 1970-01-01. -/
def localTicks (reading : LocalDateTime) : Ticks .localReading .nanosecond :=
  let seconds := reading.epochDay * 86400 +
    (reading.hour.val : Int) * 3600 + (reading.minute.val : Int) * 60 + reading.second.val
  ⟨seconds * 1000000000 + reading.nanosecond.val⟩

end LocalDateTime

/-- The supplied UTC designator or a known signed offset in whole minutes.
    The two zero-offset spellings `Z` and `+00:00` are distinguishable. -/
inductive Offset where
  | z
  | ahead (minutes : Fin 1440)
  | behind (minutes : Fin 1440) (nonzero : 0 < minutes.val)
  deriving DecidableEq, Repr

/-- The number of minutes to add to UTC to obtain the local reading. -/
def Offset.minutes : Offset → Int
  | .z => 0
  | .ahead value => value.val
  | .behind value _ => -(value.val : Int)

structure OffsetDateTime where
  reading : LocalDateTime
  offset : Offset
  deriving DecidableEq, Repr

/-- Normalize on a uniform 86,400-second day scale, retaining exact nanoseconds
    across midnight and across the epoch. -/
def OffsetDateTime.utcTicks (value : OffsetDateTime) : Ticks .utcInstant .nanosecond :=
  ⟨value.reading.localTicks.ticks - value.offset.minutes * 60000000000⟩

/-- Decode the digits following a decimal point. Excess digits are rejected
    even when they are zero. Every accepted fraction is exact. -/
def fractionNanoseconds (digits : List Char) : Except Error Nat :=
  if digits.length > 9 then .error .fractionPrecision
  else match Numeric.DecimalText.parseNat digits with
    | none => .error .syntax
    | some coefficient => .ok (coefficient * 10 ^ (9 - digits.length))

namespace Internal

def parseDigits (digits : List Char) : Except Error Nat :=
  match Numeric.DecimalText.parseNat digits with
  | none => .error .syntax
  | some n => .ok n

def parseOffset : List Char → Except Error Offset
  | ['Z'] => .ok .z
  | [sign, h₁, h₂, ':', m₁, m₂] => do
    if sign != '+' && sign != '-' then throw .syntax
    let hour ← parseDigits [h₁, h₂]
    let minute ← parseDigits [m₁, m₂]
    if h : hour < 24 ∧ minute < 60 then
      let total : Fin 1440 := ⟨hour * 60 + minute, by omega⟩
      if sign == '+' then .ok (.ahead total)
      else if nonzero : 0 < total.val then .ok (.behind total nonzero)
      else .error .invalidOffset
    else .error .invalidOffset
  | _ => .error .syntax

def parseSuffix : List Char → Except Error (Nat × Offset)
  | '.' :: rest => do
    let (digits, zone) := rest.span Char.isDigit
    let nanos ← fractionNanoseconds digits
    let offset ← parseOffset zone
    return (nanos, offset)
  | zone => do
    let offset ← parseOffset zone
    return (0, offset)

end Internal

open Internal (parseDigits parseSuffix)

/-- Parse a complete calendar datetime with an explicit known offset. -/
def parse (input : String) : Except Error OffsetDateTime :=
  match input.toList with
  | y₁ :: y₂ :: y₃ :: y₄ :: '-' :: m₁ :: m₂ :: '-' :: d₁ :: d₂ :: 'T' ::
      h₁ :: h₂ :: ':' :: i₁ :: i₂ :: ':' :: s₁ :: s₂ :: suffix => do
    let year ← parseDigits [y₁, y₂, y₃, y₄]
    let month ← parseDigits [m₁, m₂]
    let day ← parseDigits [d₁, d₂]
    let hour ← parseDigits [h₁, h₂]
    let minute ← parseDigits [i₁, i₂]
    let second ← parseDigits [s₁, s₂]
    let (nanos, offset) ← parseSuffix suffix
    let reading ← LocalDateTime.ofCivil ⟨year, month, day⟩ hour minute second nanos
    return ⟨reading, offset⟩
  | _ => .error .syntax

/-- Parse, normalize and convert exactly to a signed 64-bit UTC tick count.
    The fixed-point conversion reports sub-tick precision before overflow. -/
def parseInt64 (input : String) (unit : TickUnit) : Except Error Int64 := do
  let value ← parse input
  (value.utcTicks.toInt64 unit).mapError .conversion

end Silmaril.Formats.ISO8601
