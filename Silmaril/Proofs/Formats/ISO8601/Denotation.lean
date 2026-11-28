module

public import Silmaril.Formats.ISO8601.Defs
import Silmaril.Numeric.Gregorian.Thms
import Silmaril.Numeric.Timestamp.Thms

public section

namespace Silmaril.Proofs.Formats.ISO8601

open Silmaril.Formats.ISO8601
open Numeric.Gregorian (CivilDate)
open Numeric.Timestamp (TickUnit Ticks)

theorem ofCivil_eq_ok_iff {date : CivilDate} {hour minute second nanos : Nat}
    {reading : LocalDateTime} :
    LocalDateTime.ofCivil date hour minute second nanos = .ok reading ↔
      reading.date = date ∧ reading.hour.val = hour ∧ reading.minute.val = minute ∧
        reading.second.val = second ∧ reading.nanosecond.val = nanos := by
  constructor
  · intro success
    cases encoded : date.toEpochDay? with
    | none => simp [LocalDateTime.ofCivil, encoded] at success
    | some day =>
      simp only [LocalDateTime.ofCivil, encoded] at success
      split at success
      · cases success
        exact ⟨CivilDate.ofEpochDay_toEpochDay? encoded, rfl, rfl, rfl, rfl⟩
      · cases success
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    cases reading
    simp [LocalDateTime.ofCivil, LocalDateTime.date, CivilDate.toEpochDay?_ofEpochDay]

theorem fractionNanoseconds_eq_ok_iff {digits : List Char} {nanos : Nat} :
    fractionNanoseconds digits = .ok nanos ↔
      digits ≠ [] ∧ digits.all Char.isDigit = true ∧ digits.length ≤ 9 ∧
        nanos * 10 ^ digits.length = Nat.ofDigitChars 10 digits 0 * 10 ^ 9 := by
  by_cases length : digits.length ≤ 9
  · have scale : (10 : Nat) ^ 9 = 10 ^ (9 - digits.length) * 10 ^ digits.length := by
      rw [← Nat.pow_add, Nat.sub_add_cancel length]
    have positive : 0 < (10 : Nat) ^ digits.length := Nat.pow_pos (by decide)
    by_cases empty : digits = []
    · simp [empty, fractionNanoseconds, Numeric.DecimalText.parseNat]
    · by_cases ascii : digits.all Char.isDigit = true
      · simp [fractionNanoseconds, Numeric.DecimalText.parseNat, Numeric.DecimalText.digitsValue,
          Nat.not_lt.mpr length, empty, ascii, length, scale,
          ← Nat.mul_assoc, Nat.mul_right_cancel_iff positive]
        exact eq_comm
      · simp [fractionNanoseconds, Numeric.DecimalText.parseNat,
          Nat.not_lt.mpr length, ascii]
  · simp [fractionNanoseconds, Nat.lt_of_not_ge length, length]

theorem localTicks_epochDay (reading : LocalDateTime) :
    reading.localTicks.ticks / 86400000000000 = reading.epochDay := by
  have hour := reading.hour.isLt
  have minute := reading.minute.isLt
  have second := reading.second.isLt
  have nanos := reading.nanosecond.isLt
  simp only [LocalDateTime.localTicks]
  omega

theorem utcTicks_fraction (value : OffsetDateTime) :
    value.utcTicks.ticks % 1000000000 = value.reading.nanosecond.val := by
  have nanos := value.reading.nanosecond.isLt
  simp only [OffsetDateTime.utcTicks, LocalDateTime.localTicks]
  omega

theorem parseInt64_eq_ok_iff {input : String} {unit : TickUnit} {payload : Int64} :
    parseInt64 input unit = .ok payload ↔
      ∃ value, parse input = .ok value ∧
        payload.toInt * unit.nanosecondsPerTick + value.offset.minutes * 60000000000 =
          value.reading.localTicks.ticks := by
  cases parsed : parse input with
  | error err => simp [parseInt64, parsed, bind, Except.bind]
  | ok value =>
    have mapError_iff (result : Except Numeric.Timestamp.ConversionError Int64) :
        result.mapError Error.conversion = .ok payload ↔ result = .ok payload := by
      cases result <;> simp [Except.mapError]
    simp only [parseInt64, parsed, bind, Except.bind, Except.ok.injEq, exists_eq_left',
      mapError_iff, Ticks.toInt64_eq_ok_iff]
    constructor
    · intro h
      have ticks := congrArg Ticks.ticks h
      change (value.reading.localTicks.ticks - value.offset.minutes * 60000000000) * 1 =
        payload.toInt * unit.nanosecondsPerTick at ticks
      omega
    · intro h
      apply congrArg (fun ticks => (⟨ticks⟩ : Ticks .utcInstant .nanosecond))
      change (value.reading.localTicks.ticks - value.offset.minutes * 60000000000) * 1 =
        payload.toInt * unit.nanosecondsPerTick
      omega

end Silmaril.Proofs.Formats.ISO8601
