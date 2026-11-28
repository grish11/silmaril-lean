module

public import Silmaril.Numeric.TimeZone.Named.Defs
import Silmaril.Numeric.TimeZone.Thms

public section

namespace Silmaril.Proofs.Numeric.TimeZone.Named

open Silmaril.Numeric.TimeZone
open Silmaril.Numeric.Timestamp

theorem resolveLocal_candidates (zone : NamedZone) {unit : TickUnit} (wall : Ticks .localReading unit) :
    (zone.resolveLocal wall).candidates = zone.rules.candidates wall.denote := by
  unfold NamedZone.resolveLocal
  split <;> simp_all [LocalResolution.candidates]

theorem mem_resolveLocal_iff {zone : NamedZone} {unit : TickUnit} {wall : Ticks .localReading unit}
    {instant : UnixTime} :
    instant ∈ (zone.resolveLocal wall).candidates ↔
      zone.Supports instant ∧ zone.toLocal? instant = some wall.denote := by
  have identity : instant.denote = instant := congrArg Ticks.mk (Int.mul_one _)
  have exactImage : zone.toLocal? instant = zone.rules.toLocal? instant := by
    rw [NamedZone.toLocal?, identity]
  rw [resolveLocal_candidates, Rules.mem_candidates_iff, Rules.Matches, ← exactImage]
  constructor
  · intro h
    have existsImage : (zone.rules.toLocal? instant.denote).isSome = true := by
      change (zone.toLocal? instant).isSome = true
      simp [h]
    exact ⟨Rules.toLocal_isSome_iff.mp existsImage, h⟩
  · exact And.right

theorem resolveLocal_eq_noSolution_iff {zone : NamedZone} {unit : TickUnit}
    {wall : Ticks .localReading unit} :
    zone.resolveLocal wall = .noSolution ↔
      ∀ instant : UnixTime, zone.Supports instant → zone.toLocal? instant ≠ some wall.denote := by
  have empty : zone.resolveLocal wall = .noSolution ↔ (zone.resolveLocal wall).candidates = [] := by
    cases zone.resolveLocal wall <;> simp [LocalResolution.candidates]
  rw [empty, List.eq_nil_iff_forall_not_mem]
  simp only [mem_resolveLocal_iff, not_and]

end Silmaril.Proofs.Numeric.TimeZone.Named
