module

public import Silmaril.Numeric.UnixInterop.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Silmaril.Numeric.TimeZone.Thms
import Silmaril.Numeric.UnixClock.Thms

public section

namespace Silmaril.Proofs.Numeric.UnixInterop

open Silmaril.Numeric.UnixInterop
open Silmaril.Numeric.TimeZone Silmaril.Numeric.UnixClock

theorem exactNanoseconds_eq_some_iff {seconds : ℝ} {stamp : UnixTime} :
    exactNanoseconds? seconds = some stamp ↔ unixSeconds stamp = seconds := by
  rw [unixSeconds_nanoseconds_eq_iff]
  unfold exactNanoseconds?
  dsimp only
  split
  · rename_i hgrid
    constructor
    · intro h
      obtain rfl := Option.some.inj h
      exact hgrid
    · intro hstamp
      have hticks : ⌊seconds * 1000000000⌋ = stamp.ticks := by
        rw [← hstamp, Int.floor_intCast]
      cases stamp
      exact congrArg (fun ticks => some (⟨ticks⟩ : UnixTime)) hticks
  · rename_i hnot
    constructor
    · intro h
      cases h
    · intro hstamp
      exact (hnot (by rw [← hstamp, Int.floor_intCast])).elim

theorem readWall_eq_some_iff {clock : Convention} {rules : Rules} {t : clock.domain}
    {wall : WallTime} :
    readWall? clock rules t = some wall ↔
      ∃ stamp, unixSeconds stamp = clock.forward t ∧ rules.toLocal? stamp = some wall := by
  simp only [readWall?, Option.bind_eq_some_iff, exactNanoseconds_eq_some_iff]

theorem readWall_supported_iff {clock : Convention} {rules : Rules} {t : clock.domain} :
    (readWall? clock rules t).isSome = true ↔
      ∃ stamp, unixSeconds stamp = clock.forward t ∧ rules.Supports stamp := by
  simp only [Option.isSome_iff_exists, readWall_eq_some_iff]
  constructor
  · rintro ⟨wall, stamp, grid, reading⟩
    exact ⟨stamp, grid, Rules.toLocal_isSome_iff.mp (by rw [reading]; rfl)⟩
  · rintro ⟨stamp, grid, support⟩
    obtain ⟨wall, reading⟩ := Option.isSome_iff_exists.mp (Rules.toLocal_isSome_iff.mpr support)
    exact ⟨wall, stamp, grid, reading⟩

theorem mem_physicalCandidates_iff {clock : Convention} {rules : Rules} {wall : WallTime}
    {t : ℝ} :
    t ∈ physicalCandidates clock rules wall ↔
      ∃ h : t ∈ clock.domain, readWall? clock rules ⟨t, h⟩ = some wall := by
  constructor
  · rintro ⟨stamp, candidate, support, clockReading⟩
    exact ⟨support, readWall_eq_some_iff.mpr
      ⟨stamp, clockReading.symm, Rules.mem_candidates_iff.mp candidate⟩⟩
  · rintro ⟨support, reading⟩
    obtain ⟨stamp, grid, wallReading⟩ := readWall_eq_some_iff.mp reading
    exact ⟨stamp, Rules.mem_candidates_iff.mpr wallReading, support, grid.symm⟩

theorem readCivil_eq_some_iff {clock : Convention} {rules : Rules} {t : clock.domain}
    {civil : CivilReading} :
    readCivil? clock rules t = some civil ↔
      ∃ wall, civil.toWall? = some wall ∧ t.val ∈ physicalCandidates clock rules wall := by
  constructor
  · intro reading
    obtain ⟨wall, hw, rfl⟩ := Option.map_eq_some_iff.mp reading
    exact ⟨wall, CivilReading.toWall_ofWall wall, mem_physicalCandidates_iff.mpr ⟨t.property, hw⟩⟩
  · rintro ⟨wall, valid, candidate⟩
    obtain ⟨_, reading⟩ := mem_physicalCandidates_iff.mp candidate
    change readWall? clock rules t = some wall at reading
    simp [readCivil?, reading, CivilReading.ofWall_toWall valid]

end Silmaril.Proofs.Numeric.UnixInterop
