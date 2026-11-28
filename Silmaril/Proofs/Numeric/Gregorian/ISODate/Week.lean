module

public import Silmaril.Numeric.Gregorian.ISODate.Defs
import Silmaril.Numeric.Gregorian.Thms

public section

namespace Silmaril.Proofs.Numeric.Gregorian.ISODate

open Silmaril.Numeric.Gregorian

private theorem weekStart_bounds (year : Int) :
    yearStart year - 3 ≤ weekYearStart year ∧ weekYearStart year ≤ yearStart year + 3 := by
  dsimp only [weekYearStart]
  omega

private theorem weekStart_aligned (year : Int) : (weekYearStart year + 3) % 7 = 0 := by
  dsimp only [weekYearStart]
  omega

private theorem year_length_lower (year : Int) : (365 : Int) ≤ yearStart (year + 1) - yearStart year := by
  rw [yearStart_succ]
  unfold daysInYear
  split <;> omega

private theorem weekYear_span (year : Int) :
    weekYearStart (year + 1) - weekYearStart year = 7 * weeksInYear year ∧
    52 ≤ weeksInYear year ∧ weeksInYear year ≤ 53 := by
  have align₁ := weekStart_aligned year
  have align₂ := weekStart_aligned (year + 1)
  have bounds₁ := weekStart_bounds year
  have bounds₂ := weekStart_bounds (year + 1)
  have step := yearStart_succ year
  unfold daysInYear at step
  unfold weeksInYear
  split at step <;> omega

theorem weeksInYear_eq (year : Int) : weeksInYear year = 52 ∨ weeksInYear year = 53 := by
  have := (weekYear_span year).2
  omega

private theorem weekStart_strictMono : StrictMono weekYearStart := by
  apply strictMono_int_of_lt_succ
  intro year
  obtain ⟨span, lo, _⟩ := weekYear_span year
  omega

private theorem weekYear_bracket (day : Int) :
    weekYearStart (WeekDate.weekYear day) ≤ day ∧ day < weekYearStart (WeekDate.weekYear day + 1) := by
  let year := (CivilDate.ofEpochDay day).year
  obtain ⟨janLo, janHi⟩ := (CivilDate.ofEpochDay_year_eq_iff (day := day) (year := year)).mp rfl
  change weekYearStart (if day < weekYearStart year then year - 1
    else if weekYearStart (year + 1) ≤ day then year + 1 else year) ≤ day ∧
    day < weekYearStart ((if day < weekYearStart year then year - 1
      else if weekYearStart (year + 1) ≤ day then year + 1 else year) + 1)
  by_cases prev : day < weekYearStart year
  · have shift : year - 1 + 1 = year := by omega
    have growth := year_length_lower (year - 1)
    rw [shift] at growth
    have bound := (weekStart_bounds (year - 1)).2
    simp only [ite_eq_left prev, shift]
    omega
  · by_cases next : weekYearStart (year + 1) ≤ day
    · have growth := year_length_lower (year + 1)
      have bound := (weekStart_bounds (year + 1 + 1)).1
      simp only [ite_eq_right prev, ite_eq_left next]
      omega
    · simp only [ite_eq_right prev, ite_eq_right next]
      omega

private theorem weekYear_eq_iff {day year : Int} : WeekDate.weekYear day = year ↔
    weekYearStart year ≤ day ∧ day < weekYearStart (year + 1) := by
  constructor
  · rintro rfl
    exact weekYear_bracket day
  · intro ⟨lo, hi⟩
    obtain ⟨decodedLo, decodedHi⟩ := weekYear_bracket day
    rcases lt_trichotomy (WeekDate.weekYear day) year with before | same | after
    · have := weekStart_strictMono.monotone (show WeekDate.weekYear day + 1 ≤ year by omega)
      omega
    · exact same
    · have := weekStart_strictMono.monotone (show year + 1 ≤ WeekDate.weekYear day by omega)
      omega

private theorem week_spec (day : Int) :
    (WeekDate.ofEpochDay day).Valid ∧
    weekYearStart (WeekDate.ofEpochDay day).year + 7 * ((WeekDate.ofEpochDay day).week - (1 : Int)) +
      (WeekDate.ofEpochDay day).weekday - 1 = day := by
  let year := WeekDate.weekYear day
  let start := weekYearStart year
  let offset := day - start
  obtain ⟨lo, hi⟩ := weekYear_bracket day
  have span := (weekYear_span year).1
  change (1 ≤ (offset / 7 + 1).toNat ∧ (offset / 7 + 1).toNat ≤ weeksInYear year ∧
    1 ≤ (offset % 7 + 1).toNat ∧ (offset % 7 + 1).toNat ≤ 7) ∧
    start + 7 * ((((offset / 7 + 1).toNat : Int)) - 1) + ((offset % 7 + 1).toNat : Int) - 1 = day
  dsimp only [offset, start, year] at span ⊢
  omega

theorem week_toEpochDay_ofEpochDay (day : Int) : (WeekDate.ofEpochDay day).toEpochDay? = some day := by
  rw [WeekDate.toEpochDay?, ite_eq_left (week_spec day).1, (week_spec day).2]

theorem week_ofEpochDay_toEpochDay {date : WeekDate} {day : Int} (h : date.toEpochDay? = some day) :
    WeekDate.ofEpochDay day = date := by
  unfold WeekDate.toEpochDay? at h
  split at h
  next valid =>
    obtain ⟨lo, hi, weekdayLo, weekdayHi⟩ := valid
    have sameDay := Option.some.inj h
    have span := (weekYear_span date.year).1
    have sameYear : WeekDate.weekYear day = date.year := weekYear_eq_iff.mpr ⟨by omega, by omega⟩
    have split := (Int.ediv_emod_unique
      (a := day - weekYearStart date.year) (q := (date.week : Int) - 1)
      (r := (date.weekday : Int) - 1) (b := 7) (by decide)).mpr ⟨by omega, by omega, by omega⟩
    have sameWeek : (((date.week : Int) - 1) + 1).toNat = date.week := by omega
    have sameWeekday : (((date.weekday : Int) - 1) + 1).toNat = date.weekday := by omega
    simp only [WeekDate.ofEpochDay, sameYear, split.1, split.2, sameWeek, sameWeekday]
  next => contradiction

end Silmaril.Proofs.Numeric.Gregorian.ISODate
