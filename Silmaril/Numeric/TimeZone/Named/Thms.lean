module

public import Silmaril.Numeric.TimeZone.Named.Defs
import Silmaril.Numeric.TimeZone.Thms
import Silmaril.Proofs.Numeric.TimeZone.Named.Resolution

public section

namespace Silmaril.Numeric.TimeZone.NamedZone

open Timestamp

/-- A table is admitted exactly when its support and mapped cuts are strictly ordered. -/
theorem ofTransitions_isSome_iff (name : String) (start stop : Ticks .utcInstant .second)
    (initial : Int) (transitions : List SecondTransition) :
    (ofTransitions? name start stop initial transitions).isSome = true ↔
      Schedule.Ordered start.denote stop.denote (transitions.map SecondTransition.toTransition) := by
  unfold ofTransitions?
  split <;> simp_all

/-- The forward function is defined exactly over the declared half-open support. -/
theorem toLocal_isSome_iff {zone : NamedZone} {unit : TickUnit} {instant : Ticks .utcInstant unit} :
    (zone.toLocal? instant).isSome = true ↔ zone.Supports instant :=
  Rules.toLocal_isSome_iff

/-- Classification preserves the underlying list, including every fold candidate. -/
theorem resolveLocal_candidates (zone : NamedZone) {unit : TickUnit} (wall : Ticks .localReading unit) :
    (zone.resolveLocal wall).candidates = zone.rules.candidates wall.denote :=
  Proofs.Numeric.TimeZone.Named.resolveLocal_candidates zone wall

/-- The returned candidates are exactly the covered instants whose forward image
    is the supplied wall reading at nanosecond precision. -/
theorem mem_resolveLocal_iff {zone : NamedZone} {unit : TickUnit} {wall : Ticks .localReading unit}
    {instant : UnixTime} : instant ∈ (zone.resolveLocal wall).candidates ↔
      zone.Supports instant ∧ zone.toLocal? instant = some wall.denote :=
  Proofs.Numeric.TimeZone.Named.mem_resolveLocal_iff

/-- No solution means the supplied interval contains no exact preimage. -/
theorem resolveLocal_eq_noSolution_iff {zone : NamedZone} {unit : TickUnit}
    {wall : Ticks .localReading unit} : zone.resolveLocal wall = .noSolution ↔
      ∀ instant : UnixTime, zone.Supports instant → zone.toLocal? instant ≠ some wall.denote :=
  Proofs.Numeric.TimeZone.Named.resolveLocal_eq_noSolution_iff

/-- Candidate order is strictly increasing in nominal Unix time. -/
theorem resolveLocal_pairwise (zone : NamedZone) {unit : TickUnit} (wall : Ticks .localReading unit) :
    (zone.resolveLocal wall).candidates.Pairwise (fun first second => first.ticks < second.ticks) := by
  rw [resolveLocal_candidates]
  exact Rules.candidates_pairwise _ _

end Silmaril.Numeric.TimeZone.NamedZone
