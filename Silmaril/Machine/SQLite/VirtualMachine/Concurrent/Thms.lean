module

public import Silmaril.Machine.SQLite.VirtualMachine.Concurrent.Defs
import Silmaril.Proofs.Machine.SQLite.VirtualMachine.Concurrent
import Silmaril.Semantics.TrackA.Interaction.UB.Thms

public section

namespace Silmaril.Machine.SQLite.VirtualMachine.Concurrent

open Silmaril.Semantics.TrackA
open Silmaril.Semantics.TrackA.Interaction

variable {Thread : Type} [DecidableEq Thread]
variable {profile : Concurrency.RaceProfile} {clients : Thread → Client}
variable {versions : Nat → Database} {generation : Nat}

theorem simulate_ordinary_iff {observed : Report Thread} :
    some observed ∈ explicit profile clients versions generation ↔
      ∃ schedule, simulate profile clients versions generation schedule = some (some observed) :=
  Proofs.Machine.SQLite.VirtualMachine.Concurrent.simulate_ordinary_iff

theorem simulate_ub_iff :
    none ∈ explicit profile clients versions generation ↔
      ∃ schedule, simulate profile clients versions generation schedule = some none :=
  Proofs.Machine.SQLite.VirtualMachine.Concurrent.simulate_ub_iff

theorem raceSafe_iff :
    Concurrency.RaceSafe profile (initialConfig clients generation) ↔
      none ∉ explicit profile clients versions generation :=
  not_exists.symm

theorem catastrophic_eq_top_iff :
    catastrophic profile clients versions generation = ⊤ ↔
      none ∈ explicit profile clients versions generation :=
  UB.collapse_eq_top_iff _

theorem catastrophic_val_of_safe
    (safe : Concurrency.RaceSafe profile (initialConfig clients generation)) :
    (catastrophic profile clients versions generation).val =
      explicit profile clients versions generation :=
  UB.val_collapse_of_safe _ (raceSafe_iff.mp safe)

end Silmaril.Machine.SQLite.VirtualMachine.Concurrent
