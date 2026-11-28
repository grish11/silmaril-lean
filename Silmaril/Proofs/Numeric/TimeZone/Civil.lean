module

public import Silmaril.Numeric.TimeZone.Defs
import Silmaril.Numeric.Gregorian.Thms

public section

namespace Silmaril.Proofs.Numeric.TimeZone

open Silmaril.Numeric.TimeZone

theorem toWall_ofWall (wall : WallTime) : (CivilReading.ofWall wall).toWall? = some wall := by
  have dayPositive : 0 < nanosecondsPerDay := by decide
  have nonnegative := Int.emod_nonneg wall.ticks (Int.ne_of_gt dayPositive)
  have below := Int.emod_lt_of_pos wall.ticks dayPositive
  have reconstruct : wall.ticks / nanosecondsPerDay * nanosecondsPerDay +
      wall.ticks % nanosecondsPerDay = wall.ticks := by
    rw [Int.add_comm]
    exact Int.emod_add_ediv_mul _ _
  simp [CivilReading.ofWall, CivilReading.toWall?,
    Numeric.Gregorian.CivilDate.toEpochDay?_ofEpochDay, nonnegative, below, reconstruct]

theorem ofWall_toWall {civil : CivilReading} {wall : WallTime}
    (h : civil.toWall? = some wall) : CivilReading.ofWall wall = civil := by
  rcases civil with ⟨date, nanos⟩
  unfold CivilReading.toWall? at h
  cases hDay : date.toEpochDay? with
  | none => simp [hDay] at h
  | some day =>
    simp only [hDay] at h
    split at h
    next range =>
      obtain ⟨nonnegative, below⟩ := range
      have dayPositive : 0 < nanosecondsPerDay := by decide
      have quotient : (day * nanosecondsPerDay + nanos) / nanosecondsPerDay = day := by
        rw [Int.mul_add_ediv_right _ _ (Int.ne_of_gt dayPositive),
          Int.ediv_eq_zero_of_lt nonnegative below, Int.add_zero]
      have remainder : (day * nanosecondsPerDay + nanos) % nanosecondsPerDay = nanos := by
        rw [Int.add_comm, Int.add_mul_emod_self_right, Int.emod_eq_of_lt nonnegative below]
      cases Option.some.inj h
      simp [CivilReading.ofWall, quotient, remainder,
        Numeric.Gregorian.CivilDate.ofEpochDay_toEpochDay? hDay]
    next => contradiction

end Silmaril.Proofs.Numeric.TimeZone
