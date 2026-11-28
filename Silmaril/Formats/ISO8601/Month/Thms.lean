module

public import Silmaril.Formats.ISO8601.Month.Defs
import Silmaril.Proofs.Formats.ISO8601.Month

public section

namespace Silmaril.Formats.ISO8601

open Numeric.Gregorian (CivilMonth)

/-- An accepted input is exactly the canonical rendering of that month. -/
theorem parseMonth_eq_some_iff {input : String} {value : CivilMonth} :
    parseMonth? input = some value ↔ renderMonth? value = some input :=
  ⟨Proofs.Formats.ISO8601.Month.renderMonth_parse, Proofs.Formats.ISO8601.Month.parseMonth_render⟩

/-- The four-digit range is a condition of the text renderer. -/
theorem renderMonth_eq_some_iff {input : String} {value : CivilMonth} :
    renderMonth? value = some input ↔
      (0 ≤ value.year ∧ value.year < 10000 ∧ value.Valid) ∧
        String.ofList (Internal.monthChars value) = input := by
  by_cases fits : 0 ≤ value.year ∧ value.year < 10000 ∧ value.Valid <;> simp [renderMonth?, fits]

/-- Accepted text consumes the entire seven-character representation. -/
theorem parseMonth_length {input : String} {value : CivilMonth}
    (accepted : parseMonth? input = some value) : input.length = 7 :=
  Proofs.Formats.ISO8601.Month.parseMonth_length accepted

end Silmaril.Formats.ISO8601
