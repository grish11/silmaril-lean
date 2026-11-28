module

public import Silmaril.Formats.ISO8601.UTCText.Defs
import Silmaril.Numeric.DecimalTextProperties
import Silmaril.Numeric.Gregorian.Thms
import Silmaril.Numeric.Timestamp.Thms
import Silmaril.Numeric.UnixRepresentation.Thms
import Mathlib.Data.List.Basic
import Mathlib.Data.List.TakeDrop

public section

namespace Silmaril.Proofs.Formats.ISO8601.UTCText

open Silmaril.Formats.ISO8601
open Silmaril.Formats.ISO8601.UTCText (Error fractionWidth format formatInt64)
open Silmaril.Formats.ISO8601.UTCText.Internal (paddedDigits suffix civilChars)
open Silmaril.Numeric.DecimalText
  (Digits digits_zeros digits_repr parseNat parseNat_digits digitsValue_append digitsValue_zeros digitsValue)
open Silmaril.Numeric.Gregorian (CivilDate daysInMonth_eq)
open Silmaril.Numeric.Timestamp (Ticks TickUnit)
open Silmaril.Numeric.UnixRepresentation (CivilTime Timespec)

private theorem paddedDigits_spec {width value : Nat} (positive : 0 < width)
    (bound : value < 10 ^ width) :
    (paddedDigits width value).length = width ∧ Digits (paddedDigits width value) ∧
      parseNat (paddedDigits width value) = some value := by
  have fits := (Nat.length_toDigits_le_iff (by decide : 1 < 10) positive).mpr bound
  have length : (paddedDigits width value).length = width := by
    simp [paddedDigits, Nat.sub_add_cancel fits]
  have valid : Digits (paddedDigits width value) := by
    apply Digits.append (digits_zeros _)
    simpa only [Nat.toString_eq_repr, Nat.toList_repr] using digits_repr value
  have nonempty : paddedDigits width value ≠ [] := by
    intro empty
    simp [empty] at length
    omega
  refine ⟨length, valid, ?_⟩
  rw [parseNat_digits _ valid nonempty, paddedDigits, digitsValue_append, digitsValue_zeros]
  simp [digitsValue, Nat.ofDigitChars_ten_toDigits]

private theorem parseFraction_padded {width value : Nat} (positive : 0 < width)
    (small : width ≤ 9) (bound : value < 10 ^ width) :
    Internal.parseSuffix ('.' :: (paddedDigits width value ++ ['Z'])) =
      .ok (value * 10 ^ (9 - width), .z) := by
  obtain ⟨length, digits, parsed⟩ := paddedDigits_spec positive bound
  have span : (paddedDigits width value ++ ['Z']).span Char.isDigit =
      (paddedDigits width value, ['Z']) := by
    rw [List.span_eq_takeWhile_dropWhile, List.takeWhile_append_of_pos digits,
      List.dropWhile_append_of_pos digits]
    simp [List.takeWhile, List.dropWhile]
  rw [Internal.parseSuffix, span]
  simp [fractionNanoseconds, length, Nat.not_lt_of_ge small, parsed,
    Internal.parseOffset, bind, Except.bind, pure, Except.pure]

private theorem parseSuffix_render (unit : TickUnit) (nanos : Fin 1000000000)
    (exactFraction : 10 ^ (9 - fractionWidth unit) ∣ nanos.val) :
    Internal.parseSuffix (suffix unit nanos.val) = .ok (nanos.val, .z) := by
  let width := fractionWidth unit
  have widthBound : width ≤ 9 := by cases unit <;> decide
  by_cases noFraction : width = 0
  · have zero : nanos.val = 0 := by
      have multiple := exactFraction
      change 10 ^ (9 - width) ∣ nanos.val at multiple
      rw [noFraction] at multiple
      exact Nat.eq_zero_of_dvd_of_lt multiple nanos.isLt
    simp [suffix, show fractionWidth unit = 0 from noFraction, zero, Internal.parseSuffix,
      Internal.parseOffset, bind, Except.bind, pure, Except.pure]
  · have scale : 10 ^ width * 10 ^ (9 - width) = (10 : Nat) ^ 9 := by
      rw [← Nat.pow_add, Nat.add_sub_of_le widthBound]
    have bound : nanos.val / 10 ^ (9 - width) < 10 ^ width :=
      (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))).mpr (by rw [scale]; exact nanos.isLt)
    unfold suffix
    change Internal.parseSuffix
      (if width = 0 then ['Z'] else '.' :: (paddedDigits width (nanos.val / 10 ^ (9 - width)) ++ ['Z'])) =
        .ok (nanos.val, .z)
    simp only [noFraction, ite_false]
    rw [parseFraction_padded (Nat.pos_of_ne_zero noFraction) widthBound bound, Nat.div_mul_cancel exactFraction]

private theorem fraction_dvd (unit : TickUnit) (value : Ticks .utcInstant unit) :
    10 ^ (9 - fractionWidth unit) ∣ (CivilTime.ofTicks value).nanosecond.val := by
  have scale : (10 : Nat) ^ (9 - fractionWidth unit) = unit.nanosecondsPerTick.toNat := by
    cases unit <;> decide
  have scaleNonnegative : 0 ≤ unit.nanosecondsPerTick := by cases unit <;> decide
  have dividesSecond : unit.nanosecondsPerTick ∣ (1000000000 : Int) := by cases unit <;> decide
  have dividesTicks : unit.nanosecondsPerTick ∣ value.denote.ticks :=
    ⟨value.ticks, Int.mul_comm _ _⟩
  have remainder := Int.emod_emod_of_dvd value.denote.ticks dividesSecond
  rw [Int.emod_eq_zero_of_dvd dividesTicks] at remainder
  rw [scale]
  change _ ∣ (value.denote.ticks % (1000000000 : Int)).toNat
  apply Nat.dvd_of_mod_eq_zero
  rw [← Int.toNat_emod (Int.emod_nonneg _ (by decide)) scaleNonnegative, remainder]
  rfl

private theorem parseCivil (unit : TickUnit) (civil : CivilTime)
    (yearBound : 0 ≤ civil.date.year ∧ civil.date.year < 10000)
    (valid : civil.date.Valid) (clock : civil.hour < 24 ∧ civil.minute < 60 ∧ civil.second < 60)
    (exactFraction : 10 ^ (9 - fractionWidth unit) ∣ civil.nanosecond.val) :
    parse (String.ofList (civilChars unit civil)) =
      (LocalDateTime.ofCivil civil.date civil.hour civil.minute civil.second civil.nanosecond.val).map
        (fun reading => ⟨reading, .z⟩) := by
  have monthBound : civil.date.month < 100 := by have := valid.2.1; omega
  have dayBound : civil.date.day < 100 := by
    have upper := valid.2.2.2
    rw [daysInMonth_eq] at upper
    split_ifs at upper <;> omega
  have naturalYear : (civil.date.year.toNat : Int) = civil.date.year := Int.toNat_of_nonneg yearBound.1
  have yearFits : civil.date.year.toNat < 10 ^ 4 := by omega
  obtain ⟨yearLength, _, yearRead⟩ := paddedDigits_spec (by decide : 0 < 4) yearFits
  obtain ⟨monthLength, _, monthRead⟩ := paddedDigits_spec (by decide : 0 < 2) monthBound
  obtain ⟨dayLength, _, dayRead⟩ := paddedDigits_spec (by decide : 0 < 2) dayBound
  obtain ⟨hourLength, _, hourRead⟩ :=
    paddedDigits_spec (by decide : 0 < 2) (show civil.hour < 100 by omega)
  obtain ⟨minuteLength, _, minuteRead⟩ :=
    paddedDigits_spec (by decide : 0 < 2) (show civil.minute < 100 by omega)
  obtain ⟨secondLength, _, secondRead⟩ :=
    paddedDigits_spec (by decide : 0 < 2) (show civil.second < 100 by omega)
  obtain ⟨y₁, y₂, y₃, y₄, yearChars⟩ := List.length_eq_four.mp yearLength
  obtain ⟨m₁, m₂, monthChars⟩ := List.length_eq_two.mp monthLength
  obtain ⟨d₁, d₂, dayChars⟩ := List.length_eq_two.mp dayLength
  obtain ⟨h₁, h₂, hourChars⟩ := List.length_eq_two.mp hourLength
  obtain ⟨i₁, i₂, minuteChars⟩ := List.length_eq_two.mp minuteLength
  obtain ⟨s₁, s₂, secondChars⟩ := List.length_eq_two.mp secondLength
  rw [yearChars] at yearRead
  rw [monthChars] at monthRead
  rw [dayChars] at dayRead
  rw [hourChars] at hourRead
  rw [minuteChars] at minuteRead
  rw [secondChars] at secondRead
  have dateEq : (⟨civil.date.year, civil.date.month, civil.date.day⟩ : CivilDate) = civil.date := by
    cases civil.date
    rfl
  simp [civilChars, yearChars, monthChars, dayChars, hourChars, minuteChars, secondChars,
    parse, Internal.parseDigits, yearRead, monthRead, dayRead, hourRead, minuteRead, secondRead,
    parseSuffix_render unit civil.nanosecond exactFraction, naturalYear, dateEq,
    bind, Except.bind, Except.map, pure, Except.pure]

theorem format_eq_error_iff {unit : TickUnit} (value : Ticks .utcInstant unit) (year : Int) :
    format value = .error (.yearOutOfRange year) ↔
      year = (CivilTime.ofTicks value).date.year ∧ (year < 0 ∨ 10000 ≤ year) := by
  by_cases inRange : 0 ≤ (CivilTime.ofTicks value).date.year ∧ (CivilTime.ofTicks value).date.year < 10000
  · simp [format, inRange]
    omega
  · simp [format, inRange]
    omega

private theorem parse_format_denote {unit : TickUnit} {value : Ticks .utcInstant unit} {text : String}
    (written : format value = .ok text) :
    ∃ parsed, parse text = .ok parsed ∧ parsed.offset = .z ∧ parsed.utcTicks = value.denote := by
  let civil := CivilTime.ofTicks value
  let spec := Timespec.ofTicks value
  have specRead : civil.toTimespec? .utcInstant = some spec := CivilTime.toTimespec?_ofTimespec spec
  change (if 0 ≤ civil.date.year ∧ civil.date.year < 10000 then
    Except.ok (String.ofList (civilChars unit civil)) else
      Except.error (Error.yearOutOfRange civil.date.year)) = Except.ok text at written
  split at written
  · rename_i yearBound
    cases Except.ok.inj written
    cases dayRead : civil.date.toEpochDay? with
    | none => simp [CivilTime.toTimespec?, dayRead] at specRead
    | some day =>
      by_cases clock : civil.hour < 24 ∧ civil.minute < 60 ∧ civil.second < 60
      · have valid : civil.date.Valid := by
          by_contra invalid
          rw [(CivilDate.toEpochDay?_eq_none_iff _).mpr invalid] at dayRead
          contradiction
        let localReading : LocalDateTime :=
          ⟨day, ⟨civil.hour, clock.1⟩, ⟨civil.minute, clock.2.1⟩,
            ⟨civil.second, clock.2.2⟩, civil.nanosecond⟩
        have localRead : LocalDateTime.ofCivil civil.date civil.hour civil.minute civil.second
            civil.nanosecond.val = .ok localReading := by
          simp [LocalDateTime.ofCivil, dayRead, clock, civil.nanosecond.isLt, localReading]
        have specEq :
            (⟨day * 86400 + (civil.hour : Int) * 3600 + (civil.minute : Int) * 60 + civil.second,
              civil.nanosecond⟩ : Timespec .utcInstant) = spec := by
          simpa [CivilTime.toTimespec?, dayRead, clock] using specRead
        refine ⟨⟨localReading, .z⟩, ?_, rfl, ?_⟩
        · rw [parseCivil unit civil yearBound valid clock (fraction_dvd unit value), localRead]
          rfl
        · rw [← Timespec.toTicks_ofTicks value]
          change _ = spec.toTicks
          rw [← specEq]
          simp [OffsetDateTime.utcTicks, Offset.minutes, LocalDateTime.localTicks,
            localReading, Timespec.toTicks]
      · simp [CivilTime.toTimespec?, dayRead, clock] at specRead
  · contradiction

theorem parse_format {unit : TickUnit} {value : Ticks .utcInstant unit} {text : String}
    (written : format value = .ok text) :
    ∃ parsed, parse text = .ok parsed ∧ parsed.offset = .z ∧
      parsed.utcTicks.rescale unit = some value := by
  obtain ⟨parsed, read, offset, exactTicks⟩ := parse_format_denote written
  have exactDenotation : parsed.utcTicks.denote = value.denote := by
    rw [exactTicks]
    simp [Ticks.denote, Silmaril.Numeric.Timestamp.TickUnit.nanosecondsPerTick]
  exact ⟨parsed, read, offset, Ticks.rescale_eq_some_iff.mpr exactDenotation⟩

theorem parseInt64_formatInt64 {unit : TickUnit} {value : Int64} {text : String}
    (written : formatInt64 unit value = .ok text) : parseInt64 text unit = .ok value := by
  obtain ⟨parsed, read, _, exactTicks⟩ := parse_format_denote written
  have payloadRead : parsed.utcTicks.toInt64 unit = .ok value := by
    apply Ticks.toInt64_eq_ok_iff.mpr
    rw [exactTicks]
    simp [Ticks.denote, Silmaril.Numeric.Timestamp.TickUnit.nanosecondsPerTick]
  simp [parseInt64, read, payloadRead, bind, Except.bind, Except.mapError]

end Silmaril.Proofs.Formats.ISO8601.UTCText
