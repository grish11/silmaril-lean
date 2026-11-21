module

public import Silmaril.Semantics.Naming.Dependency.Defs
public import Mathlib.Data.Set.Finite.Lattice
import Silmaril.Proofs.Semantics.Naming.Dependency

public section

namespace Silmaril.Semantics.Naming.Dependency

variable {Name Obj Blob : Type} {edge : Name → Name → Prop} {root : Name}
variable {graph : Dependency Name Obj Blob}

theorem Bounded.accessible {fuel : Nat} (bounded : Bounded edge fuel root) : Acc edge root :=
  Proofs.Semantics.Naming.bounded_accessible bounded

/-- Finite branching gives a single uniform bound from rooted accessibility,
not from acyclicity alone. Finiteness is needed only below this root. -/
theorem exists_bounded_iff_acc
    (branching : ∀ ⦃parent⦄, _root_.Relation.ReflTransGen (fun p c => edge c p) root parent →
      {child | edge child parent}.Finite) : (∃ fuel, Bounded edge fuel root) ↔ Acc edge root :=
  ⟨fun ⟨_, bounded⟩ => bounded.accessible, Proofs.Semantics.Naming.exists_bounded branching⟩

theorem finite_branching (bound : graph.store.Binding) (finite : ∀ object, (graph.children object).Finite)
    (parent : Name) : {child | graph.Depends child parent}.Finite :=
  Proofs.Semantics.Naming.dependency_finite_branching bound finite parent

theorem acyclicBelow_of_accessible (access : Acc graph.Depends root) : graph.AcyclicBelow root :=
  Proofs.Semantics.Naming.acyclic_below_of_accessible access

/-- The finite set must contain *all* reachable objects, not just the keys of a
manifest or cache. This theorem does not ensure that requested payloads exist. -/
theorem accessible_of_finite_reachable (finite : {name | graph.Reachable root name}.Finite)
    (acyclic : graph.AcyclicBelow root) : Acc graph.Depends root :=
  Proofs.Semantics.Naming.accessible_of_finite_reachable finite acyclic

end Silmaril.Semantics.Naming.Dependency
