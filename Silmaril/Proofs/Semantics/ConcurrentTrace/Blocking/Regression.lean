module

import Silmaril.Semantics.ConcurrentTrace.Blocking.Thms
import Silmaril.Semantics.ConcurrentTrace.Thms

namespace Silmaril.Proofs.Semantics.ConcurrentTrace.Blocking.Regression

open Silmaril.Semantics.ConcurrentTrace
open Silmaril.Semantics.ConcurrentTrace.Blocking

private def directed : Footprint Bool Bool where
  owner := id
  blocks a := {name | a = false ∧ name = true}

-- Distinct owners and a single directed block suffice to prevent commutation.
example : directed.owner false ≠ directed.owner true ∧
    directed.owner true ∈ directed.blocks false ∧ directed.owner false ∉ directed.blocks true :=
  ⟨Bool.noConfusion, ⟨rfl, rfl⟩, fun h => Bool.noConfusion h.1⟩

example : TraceMonoid.singleton directed.Independent false *
      TraceMonoid.singleton directed.Independent true ≠
    TraceMonoid.singleton directed.Independent true *
      TraceMonoid.singleton directed.Independent false := by
  intro h
  rcases (directed.singleton_mul_comm_iff false true).mp h with heq | hind
  · cases heq
  · exact hind.2.2 ⟨rfl, rfl⟩

private abbrev legacy := eventSync Bool Unit

-- Disjoint participant lists still give distinct synchronization letters that cannot commute.
example : TraceMonoid.ofWord legacy.Independent [.inr [false], .inr [true]] ≠
    TraceMonoid.ofWord legacy.Independent [.inr [true], .inr [false]] := by
  intro h
  rcases (legacy.singleton_mul_comm_iff (.inr [false]) (.inr [true])).mp h with heq | hind
  · cases heq
  · exact eventSync_syncs_dependent _ _ hind

-- Lists with the same membership remain distinct labels in the quotient.
example : TraceMonoid.ofWord legacy.Independent [.inr [false, true]] ≠
    TraceMonoid.ofWord legacy.Independent [.inr [true, false, false]] := by
  intro h
  have hEncoded : eventSyncEquiv (singleton (Letter.sync (Event := Unit) [false, true])) =
      eventSyncEquiv (singleton (Letter.sync (Event := Unit) [true, false, false])) := h
  have hsync := congrArg (fun x => (syncs x).toList) (eventSyncEquiv.injective hEncoded)
  simp at hsync

-- Renaming retains the participant list while the payload map changes ordinary events.
example :
    eventSyncMap some (Option.some_injective Bool) (fun _ : Unit => 0) (TraceMonoid.ofWord
      legacy.Independent [.inr [true, false, true], .inl (false, ())]) =
    TraceMonoid.ofWord (eventSync (Option Bool) Nat).Independent
      [.inr [some true, some false, some true], .inl (some false, 0)] :=
  TraceMonoid.map_ofWord _ _ _

end Silmaril.Proofs.Semantics.ConcurrentTrace.Blocking.Regression
