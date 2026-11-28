module

public import Silmaril.Formats.ISO8601.Month.Defs
import Silmaril.Proofs.Formats.ISO8601.Date.Digits

public section

namespace Silmaril.Proofs.Formats.ISO8601.Month

open Silmaril.Formats.ISO8601
open Silmaril.Formats.ISO8601.Internal (monthChars)
open Silmaril.Numeric.Gregorian (CivilMonth)
open Silmaril.Proofs.Formats.ISO8601.Date (fixedDigits_length parseFixed_fixedDigits parseFixed_spec)

theorem parseMonth_render {input : String} {value : CivilMonth}
    (h : renderMonth? value = some input) : parseMonth? input = some value := by
  unfold renderMonth? at h
  split at h
  next fits =>
    cases Option.some.inj h
    have yearBound : value.year.toNat < 10 ^ 4 := by have := fits.2.1; omega
    have monthBound : value.month < 10 ^ 2 := by have := fits.2.2.2; omega
    have year := parseFixed_fixedDigits (by decide : 0 < 4) yearBound
    have month := parseFixed_fixedDigits (by decide : 0 < 2) monthBound
    have yearEq := Int.toNat_of_nonneg fits.1
    cases value
    simp only [parseMonth?, monthChars, String.toList_ofList,
      List.drop_left' (fixedDigits_length 4 _), List.take_left' (fixedDigits_length 4 _)]
    simp only at year month yearEq fits
    simp [year, month, yearEq, fits.2.2]
  next => contradiction

theorem renderMonth_parse {input : String} {value : CivilMonth}
    (h : parseMonth? input = some value) : renderMonth? value = some input := by
  unfold parseMonth? at h
  dsimp only at h
  split at h
  next tail suffix =>
    simp only [Bind.bind, Option.bind_eq_some_iff] at h
    obtain ⟨year, hy, month, hm, result⟩ := h
    split at result
    next valid =>
      cases Option.some.inj result
      obtain ⟨bound, yearText⟩ := parseFixed_spec hy
      have monthText := (parseFixed_spec hm).2
      have chars : monthChars ⟨year, month⟩ = input.toList := by
        simp only [monthChars, Int.toNat_natCast, yearText, monthText, ← suffix,
          List.take_append_drop]
      have yearFits : (year : Int) < 10000 := by omega
      simp [renderMonth?, valid, yearFits, chars, String.ofList_toList]
    next => contradiction
  next => contradiction

theorem parseMonth_length {input : String} {value : CivilMonth}
    (h : parseMonth? input = some value) : input.length = 7 := by
  have printed := renderMonth_parse h
  unfold renderMonth? at printed
  split at printed
  next =>
    cases Option.some.inj printed
    have dash : "-".length = 1 := by decide
    simp [monthChars, fixedDigits_length, dash]
  next => contradiction

end Silmaril.Proofs.Formats.ISO8601.Month
