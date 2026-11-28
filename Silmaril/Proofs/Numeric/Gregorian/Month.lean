module

public import Silmaril.Numeric.Gregorian.Month.Defs
import Silmaril.Numeric.Gregorian.Thms
import Silmaril.Proofs.Numeric.Gregorian.Conversion

public section

namespace Silmaril.Proofs.Numeric.Gregorian.Month

open Silmaril.Numeric.Gregorian
open Silmaril.Numeric.Gregorian.CivilMonth
open Silmaril.Numeric.Gregorian.Internal (monthStart)

private theorem daysInMonth_pos {value : CivilMonth} (valid : value.Valid) :
    1 ≤ daysInMonth value.year value.month := by
  change 1 ≤ value.month ∧ value.month ≤ 12 at valid
  rw [daysInMonth_eq, ite_eq_left valid]
  repeat' first | omega | split

theorem firstDay_valid_iff {value : CivilMonth} : value.firstDay.Valid ↔ value.Valid := by
  constructor
  · intro valid
    exact ⟨valid.1, valid.2.1⟩
  · intro valid
    exact ⟨valid.1, valid.2, le_rfl, daysInMonth_pos valid⟩

theorem next_valid {value : CivilMonth} (valid : value.Valid) : value.next.Valid := by
  obtain ⟨lower, upper⟩ := valid
  unfold CivilMonth.next
  split <;> simp only [CivilMonth.Valid] <;> omega

theorem interval?_eq_some_iff {value : CivilMonth} {bounds : MonthInterval} :
    value.interval? = some bounds ↔
      value.firstDay.toEpochDay? = some bounds.start ∧
      bounds.stop = bounds.start + daysInMonth value.year value.month := by
  rcases bounds with ⟨start, stop⟩
  cases encoded : value.firstDay.toEpochDay? with
  | none => simp [CivilMonth.interval?, encoded]
  | some day =>
    simp only [CivilMonth.interval?, encoded, Option.map_some, Option.some.injEq, MonthInterval.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩

theorem interval?_isSome_iff (value : CivilMonth) :
    value.interval?.isSome = true ↔ value.Valid := by
  rw [← firstDay_valid_iff]
  by_cases valid : value.firstDay.Valid <;> simp [CivilMonth.interval?, CivilDate.toEpochDay?, valid]

private theorem start_eq {value : CivilMonth} {start : Int}
    (encoded : value.firstDay.toEpochDay? = some start) :
    value.Valid ∧ start = yearStart value.year + monthStart (isLeapYear value.year) (value.month - 1) := by
  unfold CivilDate.toEpochDay? at encoded
  split at encoded
  next valid =>
    exact ⟨firstDay_valid_iff.mp valid, by
      simpa [CivilMonth.firstDay] using (Option.some.inj encoded).symm⟩
  next => cases encoded

theorem contains_iff {value : CivilMonth} {bounds : MonthInterval} {day : Int}
    (checked : value.interval? = some bounds) :
    bounds.Contains day ↔ CivilMonth.ofEpochDay day = value := by
  obtain ⟨first, stop⟩ := interval?_eq_some_iff.mp checked
  obtain ⟨valid, start⟩ := start_eq first
  constructor
  · rintro ⟨low, high⟩
    let position := (day - bounds.start).toNat + 1
    have offset : (position : Int) = day - bounds.start + 1 := by
      simp [position, Int.toNat_of_nonneg (show 0 ≤ day - bounds.start by omega)]
    let date : CivilDate := ⟨value.year, value.month, position⟩
    have hdate : date.Valid :=
      ⟨valid.1, valid.2, Nat.succ_pos _, by
        change position ≤ daysInMonth value.year value.month
        omega⟩
    have encoded : date.toEpochDay? = some day := by
      rw [CivilDate.toEpochDay?, ite_eq_left hdate, Option.some.injEq]
      change yearStart value.year + monthStart (isLeapYear value.year) (value.month - 1) +
        (position : Int) - 1 = day
      omega
    simp [CivilMonth.ofEpochDay, CivilDate.ofEpochDay_toEpochDay? encoded, date]
  · intro observed
    let date := CivilDate.ofEpochDay day
    have hdate : date.Valid := CivilDate.ofEpochDay_valid day
    have year : date.year = value.year := congrArg CivilMonth.year observed
    have month : date.month = value.month := congrArg CivilMonth.month observed
    have encoded := CivilDate.toEpochDay?_ofEpochDay day
    change date.toEpochDay? = some day at encoded
    rw [CivilDate.toEpochDay?, ite_eq_left hdate, Option.some.injEq, year, month] at encoded
    have lo := hdate.2.2.1
    have hi := hdate.2.2.2
    rw [year, month] at hi
    exact ⟨by omega, by omega⟩

theorem interval_next {value : CivilMonth} {bounds : MonthInterval}
    (checked : value.interval? = some bounds) :
    ∃ nextBounds, value.next.interval? = some nextBounds ∧ bounds.stop = nextBounds.start := by
  obtain ⟨first, stop⟩ := interval?_eq_some_iff.mp checked
  obtain ⟨valid, start⟩ := start_eq first
  obtain ⟨nextBounds, nextChecked⟩ :=
    Option.isSome_iff_exists.mp ((interval?_isSome_iff value.next).mpr (next_valid valid))
  have nextStart := (start_eq (interval?_eq_some_iff.mp nextChecked).1).2
  refine ⟨nextBounds, nextChecked, ?_⟩
  rw [stop, start, monthStart_add_daysInMonth _ _ valid, nextStart]
  by_cases last : value.month = 12 <;> simp [CivilMonth.next, last]

end Silmaril.Proofs.Numeric.Gregorian.Month
