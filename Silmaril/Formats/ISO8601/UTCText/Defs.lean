module

public import Silmaril.Formats.ISO8601.Defs
public import Silmaril.Numeric.UnixRepresentation.Defs

/-! # Canonical UTC text for exact timestamp ticks -/

@[expose] public section

namespace Silmaril.Formats.ISO8601.UTCText

open Numeric.Timestamp (Ticks TickUnit)
open Numeric.UnixRepresentation (CivilTime)

inductive Error where
  | yearOutOfRange (year : Int)
  deriving DecidableEq, Repr

/-- The decimal width of the input tick unit. Zero denotes no fractional field. -/
def fractionWidth : TickUnit → Nat
  | .second => 0
  | .millisecond => 3
  | .microsecond => 6
  | .nanosecond => 9

namespace Internal

def paddedDigits (width value : Nat) : List Char :=
  let digits := Nat.toDigits 10 value
  List.replicate (width - digits.length) '0' ++ digits

def suffix (unit : TickUnit) (nanosecond : Nat) : List Char :=
  let width := fractionWidth unit
  if width = 0 then ['Z']
  else '.' :: (paddedDigits width (nanosecond / 10 ^ (9 - width)) ++ ['Z'])

def civilChars (unit : TickUnit) (civil : CivilTime) : List Char :=
  paddedDigits 4 civil.date.year.toNat ++ ['-'] ++ paddedDigits 2 civil.date.month ++ ['-'] ++
    paddedDigits 2 civil.date.day ++ ['T'] ++ paddedDigits 2 civil.hour ++ [':'] ++
    paddedDigits 2 civil.minute ++ [':'] ++ paddedDigits 2 civil.second ++
    suffix unit civil.nanosecond.val

end Internal

/-- Format a UTC instant in the existing four-digit calendar datetime profile.
The fractional field has exactly the input unit's decimal width, including
trailing zeros. The year uses astronomical numbering. -/
def format {unit : TickUnit} (value : Ticks .utcInstant unit) : Except Error String :=
  let civil := CivilTime.ofTicks value
  if 0 ≤ civil.date.year ∧ civil.date.year < 10000 then
    .ok (String.ofList (Internal.civilChars unit civil))
  else .error (.yearOutOfRange civil.date.year)

/-- Format a signed 64-bit tick payload in its original unit. -/
def formatInt64 (unit : TickUnit) (value : Int64) : Except Error String :=
  format (Ticks.ofInt64 .utcInstant unit value)

end Silmaril.Formats.ISO8601.UTCText
