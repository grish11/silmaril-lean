module

public import Silmaril.Formats.ISO8601.Defs
import Silmaril.Proofs.Formats.ISO8601.Denotation

/-! # Denotation laws for the extended calendar date/time profile -/

public section

namespace Silmaril.Formats.ISO8601

open Numeric.Gregorian (CivilDate)
open Numeric.Timestamp (TickUnit)

/-- The checked constructor recovers precisely the supplied date and clock fields. -/
theorem LocalDateTime.ofCivil_eq_ok_iff {date : CivilDate} {hour minute second nanos : Nat}
    {reading : LocalDateTime} :
    ofCivil date hour minute second nanos = .ok reading ↔
      reading.date = date ∧ reading.hour.val = hour ∧ reading.minute.val = minute ∧
        reading.second.val = second ∧ reading.nanosecond.val = nanos :=
  Proofs.Formats.ISO8601.ofCivil_eq_ok_iff

/-- An admitted fraction represents the same rational value as the input decimal,
    expressed by cross-multiplying the powers-of-ten denominators. -/
theorem fractionNanoseconds_eq_ok_iff {digits : List Char} {nanos : Nat} :
    fractionNanoseconds digits = .ok nanos ↔
      digits ≠ [] ∧ digits.all Char.isDigit = true ∧ digits.length ≤ 9 ∧
        nanos * 10 ^ digits.length = Nat.ofDigitChars 10 digits 0 * 10 ^ 9 :=
  Proofs.Formats.ISO8601.fractionNanoseconds_eq_ok_iff

/-- Euclidean division recovers the local calendar day, including before the epoch. -/
theorem LocalDateTime.localTicks_epochDay (reading : LocalDateTime) :
    reading.localTicks.ticks / 86400000000000 = reading.epochDay :=
  Proofs.Formats.ISO8601.localTicks_epochDay reading

/-- Normalizing a whole-minute offset preserves the fraction within the second,
    including when the normalized instant is before the epoch. -/
theorem OffsetDateTime.utcTicks_fraction (value : OffsetDateTime) :
    value.utcTicks.ticks % 1000000000 = value.reading.nanosecond.val :=
  Proofs.Formats.ISO8601.utcTicks_fraction value

/-- Exact conversion succeeds precisely when the signed payload, interpreted in
    the requested unit and shifted by the supplied offset, gives the local reading. -/
theorem parseInt64_eq_ok_iff {input : String} {unit : TickUnit} {payload : Int64} :
    parseInt64 input unit = .ok payload ↔
      ∃ value, parse input = .ok value ∧
        payload.toInt * unit.nanosecondsPerTick + value.offset.minutes * 60000000000 =
          value.reading.localTicks.ticks :=
  Proofs.Formats.ISO8601.parseInt64_eq_ok_iff

end Silmaril.Formats.ISO8601
