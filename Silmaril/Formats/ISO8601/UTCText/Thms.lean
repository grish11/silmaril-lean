module

public import Silmaril.Formats.ISO8601.UTCText.Defs
import Silmaril.Proofs.Formats.ISO8601.UTCText.RoundTrip

public section

namespace Silmaril.Formats.ISO8601.UTCText

open Numeric.Timestamp (Ticks TickUnit)
open Numeric.UnixRepresentation (CivilTime)

/-- The formatter rejects exactly the UTC civil years outside 0000–9999. -/
theorem format_eq_error_iff {unit : TickUnit} (value : Ticks .utcInstant unit) (year : Int) :
    format value = .error (.yearOutOfRange year) ↔
      year = (CivilTime.ofTicks value).date.year ∧ (year < 0 ∨ 10000 ≤ year) :=
  Proofs.Formats.ISO8601.UTCText.format_eq_error_iff value year

/-- Parsing a formatted instant yields Z and recovers the original ticks in
the original unit by exact rescaling. -/
theorem parse_format {unit : TickUnit} {value : Ticks .utcInstant unit} {text : String}
    (written : format value = .ok text) :
    ∃ parsed, parse text = .ok parsed ∧ parsed.offset = .z ∧
      parsed.utcTicks.rescale unit = some value :=
  Proofs.Formats.ISO8601.UTCText.parse_format written

/-- The signed parser recovers the original payload without rounding. -/
theorem parseInt64_formatInt64 {unit : TickUnit} {value : Int64} {text : String}
    (written : formatInt64 unit value = .ok text) : parseInt64 text unit = .ok value :=
  Proofs.Formats.ISO8601.UTCText.parseInt64_formatInt64 written

end Silmaril.Formats.ISO8601.UTCText
