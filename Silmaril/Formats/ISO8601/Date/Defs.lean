module

public import Silmaril.Formats.ISO8601.Defs
public import Silmaril.Numeric.Gregorian.ISODate.Defs

/-! # Four-digit extended ordinal and ISO week dates -/

@[expose] public section

namespace Silmaril.Formats.ISO8601

open Numeric.Gregorian (OrdinalDate WeekDate)

namespace Internal

/-- The fixed number of ASCII decimal places, most significant first. -/
def fixedDigits : Nat → Nat → List Char
  | 0, _ => []
  | width + 1, value =>
    (value / 10 ^ width).digitChar :: fixedDigits width (value % 10 ^ width)

def parseFixed? (width : Nat) (digits : List Char) : Option Nat :=
  if digits.length = width then Numeric.DecimalText.parseNat digits else none

def ordinalChars (value : OrdinalDate) : List Char :=
  fixedDigits 4 value.year.toNat ++ '-' :: fixedDigits 3 value.ordinal

def weekChars (value : WeekDate) : List Char :=
  fixedDigits 4 value.year.toNat ++
    ('-' :: 'W' :: (fixedDigits 2 value.week ++ '-' :: fixedDigits 1 value.weekday))

end Internal

open Internal (parseFixed? ordinalChars weekChars)

/-- Read the complete extended ordinal form `YYYY-DDD`. -/
def parseOrdinalDate? (input : String) : Option OrdinalDate := do
  let chars := input.toList
  match chars.drop 4 with
  | '-' :: tail =>
    let year ← parseFixed? 4 (chars.take 4)
    let ordinal ← parseFixed? 3 tail
    let value : OrdinalDate := ⟨year, ordinal⟩
    if value.Valid then some value else none
  | _ => none

/-- Read the complete extended week form `YYYY-Www-D`. -/
def parseWeekDate? (input : String) : Option WeekDate := do
  let chars := input.toList
  match chars.drop 4 with
  | '-' :: 'W' :: tail =>
    match tail.drop 2 with
    | '-' :: rest =>
      let year ← parseFixed? 4 (chars.take 4)
      let week ← parseFixed? 2 (tail.take 2)
      let weekday ← parseFixed? 1 rest
      let value : WeekDate := ⟨year, week, weekday⟩
      if value.Valid then some value else none
    | _ => none
  | _ => none

/-- Write the ordinal form for valid dates with a year in 0000 through 9999. -/
def renderOrdinalDate? (value : OrdinalDate) : Option String :=
  if 0 ≤ value.year ∧ value.year < 10000 ∧ value.Valid then
    some (String.ofList (ordinalChars value))
  else none

/-- Write the week form for valid dates with a week-year in 0000 through 9999. -/
def renderWeekDate? (value : WeekDate) : Option String :=
  if 0 ≤ value.year ∧ value.year < 10000 ∧ value.Valid then
    some (String.ofList (weekChars value))
  else none

end Silmaril.Formats.ISO8601
