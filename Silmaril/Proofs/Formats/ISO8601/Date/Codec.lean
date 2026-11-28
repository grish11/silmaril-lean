module

public import Silmaril.Formats.ISO8601.Date.Defs
import Silmaril.Numeric.Gregorian.ISODate.Thms
import Silmaril.Proofs.Formats.ISO8601.Date.Digits

public section

namespace Silmaril.Proofs.Formats.ISO8601.Date

open Silmaril.Formats.ISO8601
open Silmaril.Formats.ISO8601.Internal
open Silmaril.Numeric.Gregorian

theorem parseOrdinal_render {input : String} {value : OrdinalDate}
    (h : renderOrdinalDate? value = some input) : parseOrdinalDate? input = some value := by
  unfold renderOrdinalDate? at h
  split at h
  next fits =>
    cases Option.some.inj h
    have yearBound : value.year.toNat < 10 ^ 4 := by have := fits.2.1; omega
    have ordinalBound : value.ordinal < 10 ^ 3 := by
      have bound := fits.2.2.2
      unfold daysInYear at bound
      split at bound <;> omega
    have year := parseFixed_fixedDigits (by decide : 0 < 4) yearBound
    have ordinal := parseFixed_fixedDigits (by decide : 0 < 3) ordinalBound
    have yearEq := Int.toNat_of_nonneg fits.1
    cases value
    simp only [parseOrdinalDate?, ordinalChars, String.toList_ofList,
      List.drop_left' (fixedDigits_length 4 _), List.take_left' (fixedDigits_length 4 _)]
    simp only at year ordinal yearEq fits
    simp [year, ordinal, yearEq, fits.2.2]
  next => contradiction

theorem renderOrdinal_parse {input : String} {value : OrdinalDate}
    (h : parseOrdinalDate? input = some value) : renderOrdinalDate? value = some input := by
  unfold parseOrdinalDate? at h
  dsimp only at h
  split at h
  next tail suffix =>
    simp only [Bind.bind, Option.bind_eq_some_iff] at h
    obtain ⟨year, hy, ordinal, ho, result⟩ := h
    split at result
    next valid =>
      cases Option.some.inj result
      obtain ⟨bound, yearText⟩ := parseFixed_spec hy
      have ordinalText := (parseFixed_spec ho).2
      have chars : ordinalChars ⟨year, ordinal⟩ = input.toList := by
        simp only [ordinalChars, Int.toNat_natCast, yearText, ordinalText, ← suffix,
          List.take_append_drop]
      have yearFits : (year : Int) < 10000 := by omega
      simp [renderOrdinalDate?, valid, yearFits, chars, String.ofList_toList]
    next => contradiction
  next => contradiction

theorem parseWeek_render {input : String} {value : WeekDate}
    (h : renderWeekDate? value = some input) : parseWeekDate? input = some value := by
  unfold renderWeekDate? at h
  split at h
  next fits =>
    cases Option.some.inj h
    have yearBound : value.year.toNat < 10 ^ 4 := by have := fits.2.1; omega
    have weekBound : value.week < 10 ^ 2 := by
      have bound := fits.2.2.2.1
      rcases weeksInYear_eq value.year with eq | eq <;> omega
    have weekdayBound : value.weekday < 10 ^ 1 := by have := fits.2.2.2.2.2; omega
    have year := parseFixed_fixedDigits (by decide : 0 < 4) yearBound
    have week := parseFixed_fixedDigits (by decide : 0 < 2) weekBound
    have weekday := parseFixed_fixedDigits (by decide : 0 < 1) weekdayBound
    have yearEq := Int.toNat_of_nonneg fits.1
    cases value
    simp only [parseWeekDate?, weekChars, String.toList_ofList]
    simp only at year week weekday yearEq fits
    simp [year, week, weekday, yearEq, fits.2.2]
  next => contradiction

theorem renderWeek_parse {input : String} {value : WeekDate}
    (h : parseWeekDate? input = some value) : renderWeekDate? value = some input := by
  unfold parseWeekDate? at h
  dsimp only at h
  split at h
  next tail suffix =>
    split at h
    next rest tailSuffix =>
      simp only [Bind.bind, Option.bind_eq_some_iff] at h
      obtain ⟨year, hy, week, hw, weekday, hd, result⟩ := h
      split at result
      next valid =>
        cases Option.some.inj result
        obtain ⟨bound, yearText⟩ := parseFixed_spec hy
        have weekText := (parseFixed_spec hw).2
        have weekdayText := (parseFixed_spec hd).2
        have tailText : fixedDigits 2 week ++ '-' :: fixedDigits 1 weekday = tail := by
          simp only [weekText, weekdayText, ← tailSuffix, List.take_append_drop]
        have chars : weekChars ⟨year, week, weekday⟩ = input.toList := by
          simp only [weekChars, Int.toNat_natCast, yearText, tailText, ← suffix,
            List.take_append_drop]
        have yearFits : (year : Int) < 10000 := by omega
        simp [renderWeekDate?, valid, yearFits, chars, String.ofList_toList]
      next => contradiction
    next => contradiction
  next => contradiction

end Silmaril.Proofs.Formats.ISO8601.Date
