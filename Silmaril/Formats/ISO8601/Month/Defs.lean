module

public import Silmaril.Formats.ISO8601.Date.Defs
public import Silmaril.Numeric.Gregorian.Month.Defs

/-! # Four-digit ISO 8601 month text -/

@[expose] public section

namespace Silmaril.Formats.ISO8601

open Numeric.Gregorian (CivilMonth)

namespace Internal

def monthChars (value : CivilMonth) : List Char :=
  fixedDigits 4 value.year.toNat ++ '-' :: fixedDigits 2 value.month

end Internal

open Internal (fixedDigits parseFixed? monthChars)

/-- Consume the entire reduced-precision form `YYYY-MM`. -/
def parseMonth? (input : String) : Option CivilMonth := do
  let chars := input.toList
  match chars.drop 4 with
  | '-' :: tail =>
    let year ← parseFixed? 4 (chars.take 4)
    let month ← parseFixed? 2 tail
    let value : CivilMonth := ⟨year, month⟩
    if value.Valid then some value else none
  | _ => none

/-- Write a valid month whose astronomical year fits in four digits. -/
def renderMonth? (value : CivilMonth) : Option String :=
  if 0 ≤ value.year ∧ value.year < 10000 ∧ value.Valid then
    some (String.ofList (monthChars value))
  else none

end Silmaril.Formats.ISO8601
