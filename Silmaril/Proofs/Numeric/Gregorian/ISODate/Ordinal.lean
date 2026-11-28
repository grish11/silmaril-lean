module

public import Silmaril.Numeric.Gregorian.ISODate.Defs
import Silmaril.Numeric.Gregorian.Thms

public section

namespace Silmaril.Proofs.Numeric.Gregorian.ISODate

open Silmaril.Numeric.Gregorian

private theorem ordinal_spec (day : Int) :
    (OrdinalDate.ofEpochDay day).Valid ∧
    yearStart (OrdinalDate.ofEpochDay day).year + (OrdinalDate.ofEpochDay day).ordinal - 1 = day := by
  let year := (CivilDate.ofEpochDay day).year
  have bounds := (CivilDate.ofEpochDay_year_eq_iff (day := day) (year := year)).mp rfl
  rw [yearStart_succ] at bounds
  change (1 ≤ (day - yearStart year + 1).toNat ∧ (day - yearStart year + 1).toNat ≤ daysInYear year) ∧
    yearStart year + ((day - yearStart year + 1).toNat : Int) - 1 = day
  rw [Int.toNat_of_nonneg (show 0 ≤ day - yearStart year + 1 by omega)]
  omega

theorem ordinal_toEpochDay_ofEpochDay (day : Int) :
    (OrdinalDate.ofEpochDay day).toEpochDay? = some day := by
  rw [OrdinalDate.toEpochDay?, ite_eq_left (ordinal_spec day).1, (ordinal_spec day).2]

theorem ordinal_ofEpochDay_toEpochDay {date : OrdinalDate} {day : Int}
    (h : date.toEpochDay? = some day) : OrdinalDate.ofEpochDay day = date := by
  unfold OrdinalDate.toEpochDay? at h
  split at h
  next valid =>
    have sameDay := Option.some.inj h
    have sameYear : (CivilDate.ofEpochDay day).year = date.year := by
      apply CivilDate.ofEpochDay_year_eq_iff.mpr
      rw [yearStart_succ]
      exact ⟨by have := valid.1; omega, by have := valid.2; omega⟩
    have sameOrdinal : (day - yearStart date.year + 1).toNat = date.ordinal := by omega
    simp only [OrdinalDate.ofEpochDay, sameYear, sameOrdinal]
  next => contradiction

end Silmaril.Proofs.Numeric.Gregorian.ISODate
