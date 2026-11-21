module

public import Silmaril.Formats.Dasl.Resolve.View.Defs
import Silmaril.Proofs.Formats.Dasl.View

public section

namespace Silmaril.Formats.Dasl

open Silmaril.Semantics.Naming

variable {Name : Type}

theorem Reader.binding (reader : Reader Name) : reader.store.Binding :=
  ⟨graph_binding reader.object?, graph_binding reader.blob?⟩

theorem Reader.observe_shallow (reader : Reader Name) (fuel : Nat) (tree : Shallow Name) :
    (reader.observe fuel tree).shallow = tree := Proofs.Formats.Dasl.observe_shallow reader fuel tree

theorem Reader.observe_bindings (reader : Reader Name) (fuel : Nat) (tree : Shallow Name) :
    (reader.observe fuel tree).bindings.Subset reader.store := Proofs.Formats.Dasl.observe_bindings reader fuel tree

theorem Reader.observeRoot_sound (reader : Reader Name) {fuel root result}
    (found : reader.observeRoot? fuel root = some result) : PartialNames reader.store root result := by
  obtain ⟨source, hit, rfl⟩ := Option.map_eq_some_iff.mp found
  exact ⟨(reader.observe_shallow fuel source).symm ▸ hit, reader.observe_bindings fuel source⟩

theorem Reader.observe_succ (reader : Reader Name) (fuel : Nat) (tree : Shallow Name) :
    Extends (reader.observe fuel tree) (reader.observe (fuel + 1) tree) :=
  Proofs.Formats.Dasl.observe_succ reader fuel tree

theorem Reader.observe_mono (reader : Reader Name) (tree : Shallow Name) {low high : Nat} (order : low ≤ high) :
    Extends (reader.observe low tree) (reader.observe high tree) :=
  Proofs.Formats.Dasl.observe_mono reader tree order

/-- Every finite full expansion is recovered at all sufficiently large fuel budgets. -/
theorem Reader.observeRoot_eventually (reader : Reader Name) {root target}
    (full : FullNames reader.store root target) :
    ∃ bound, ∀ fuel, bound ≤ fuel → reader.observeRoot? fuel root = some target.embed := by
  obtain ⟨source, hit, expanded⟩ := full
  obtain ⟨bound, ready⟩ := Proofs.Formats.Dasl.observe_eventually reader expanded
  exact ⟨bound, fun fuel enough => (Option.map_eq_some_iff).mpr ⟨source, hit, ready fuel enough⟩⟩

end Silmaril.Formats.Dasl
