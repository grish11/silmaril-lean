module

public import Silmaril.Formats.ISO8601.Date.Defs
import Silmaril.Proofs.Formats.ISO8601.Date.Codec

public section

namespace Silmaril.Formats.ISO8601

open Numeric.Gregorian (OrdinalDate WeekDate)

/-- Parsing and rendering agree on accepted ordinal dates and their exact spelling. -/
theorem parseOrdinalDate_eq_some_iff {input : String} {value : OrdinalDate} :
    parseOrdinalDate? input = some value ↔ renderOrdinalDate? value = some input :=
  ⟨Proofs.Formats.ISO8601.Date.renderOrdinal_parse, Proofs.Formats.ISO8601.Date.parseOrdinal_render⟩

/-- Parsing and rendering agree on accepted week dates and their exact spelling. -/
theorem parseWeekDate_eq_some_iff {input : String} {value : WeekDate} :
    parseWeekDate? input = some value ↔ renderWeekDate? value = some input :=
  ⟨Proofs.Formats.ISO8601.Date.renderWeek_parse, Proofs.Formats.ISO8601.Date.parseWeek_render⟩

/-- Only valid ordinal dates with four-digit years are representable in this profile. -/
theorem renderOrdinalDate_eq_none_iff (value : OrdinalDate) :
    renderOrdinalDate? value = none ↔ ¬ (0 ≤ value.year ∧ value.year < 10000 ∧ value.Valid) := by
  unfold renderOrdinalDate?
  split <;> simp_all

/-- Only valid week dates with four-digit week-years are representable in this profile. -/
theorem renderWeekDate_eq_none_iff (value : WeekDate) :
    renderWeekDate? value = none ↔ ¬ (0 ≤ value.year ∧ value.year < 10000 ∧ value.Valid) := by
  unfold renderWeekDate?
  split <;> simp_all

end Silmaril.Formats.ISO8601
