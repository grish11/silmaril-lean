module

public import Silmaril.Semantics.Naming.Dependency.Defs
public import Silmaril.Semantics.Naming.Thms
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Finset.Lattice.Fold

public section

namespace Silmaril.Proofs.Semantics.Naming

open Silmaril.Semantics.Naming Dependency

variable {Name Obj Blob : Type} {edge : Name → Name → Prop} {root : Name}
variable {graph : Dependency Name Obj Blob}

theorem bounded_accessible {fuel : Nat} (bounded : Bounded edge fuel root) : Acc edge root := by
  induction fuel generalizing root with
  | zero => exact .intro _ fun _ step => (bounded step).elim
  | succ _ ih => exact .intro _ fun _ step => ih (bounded step)

private theorem bounded_succ {fuel : Nat} (bounded : Bounded edge fuel root) : Bounded edge (fuel + 1) root := by
  induction fuel generalizing root with
  | zero => exact fun _ step => (bounded step).elim
  | succ _ ih => exact fun _ step => ih (bounded step)

private theorem bounded_le {low high : Nat} (order : low ≤ high) (bounded : Bounded edge low root) :
    Bounded edge high root :=
  Nat.le_induction bounded (fun _ _ step => bounded_succ step) high order

theorem exists_bounded
    (branching : ∀ ⦃parent⦄, _root_.Relation.ReflTransGen (fun p c => edge c p) root parent →
      {child | edge child parent}.Finite) (access : Acc edge root) : ∃ fuel, Bounded edge fuel root := by
  classical
  have localBound : ∀ parent, Acc edge parent →
      _root_.Relation.ReflTransGen (fun p c => edge c p) root parent → ∃ fuel, Bounded edge fuel parent := by
    intro parent reachable
    induction reachable with
    | intro parent _ ih =>
      intro path
      have childBound : ∀ child, ∃ fuel, edge child parent → Bounded edge fuel child := by
        intro child
        by_cases step : edge child parent
        · obtain ⟨fuel, bounded⟩ := ih child step (path.tail step)
          exact ⟨fuel, fun _ => bounded⟩
        · exact ⟨0, fun hit => (step hit).elim⟩
      choose depth bounded using childBound
      let support := (branching path).toFinset
      exact ⟨support.sup depth + 1, fun child step =>
        bounded_le (Finset.le_sup (f := depth) ((branching path).mem_toFinset.mpr step)) (bounded child step)⟩
  exact localBound root access .refl

theorem dependency_finite_branching (bound : graph.store.Binding) (finite : ∀ object, (graph.children object).Finite)
    (parent : Name) : {child | graph.Depends child parent}.Finite := by
  classical
  by_cases present : ∃ object, graph.store.objects parent object
  · obtain ⟨object, hit⟩ := present
    refine ((finite object).preimage (f := Sum.inl) Sum.inl_injective.injOn).subset ?_
    rintro child ⟨found, read, linked⟩
    exact bound.1 read hit ▸ linked
  · exact Set.finite_empty.subset fun _ ⟨object, hit, _⟩ => (present ⟨object, hit⟩).elim

theorem acyclic_below_of_accessible (access : Acc graph.Depends root) : graph.AcyclicBelow root := by
  intro name path cycle
  have below : Acc graph.Depends name := by
    clear cycle
    induction path with
    | refl => exact access
    | tail _ step ih => exact ih.inv step
  have noLoop : ∀ name, Acc (_root_.Relation.TransGen graph.Depends) name →
      ¬ _root_.Relation.TransGen graph.Depends name name := by
    intro vertex acc
    induction acc with
    | intro vertex _ ih => exact fun loop => ih vertex loop loop
  exact noLoop name below.transGen cycle

theorem accessible_of_finite_reachable (finite : {name | graph.Reachable root name}.Finite)
    (acyclic : graph.AcyclicBelow root) : Acc graph.Depends root := by
  let Seen := {name // graph.Reachable root name}
  let included : Seen → Seen → Prop := fun child parent => _root_.Relation.TransGen graph.Depends child.val parent.val
  let _ : Finite Seen := finite
  let _ : IsTrans Seen included := ⟨fun _ _ _ first second => first.trans second⟩
  let _ : Std.Irrefl included := ⟨fun vertex => acyclic vertex.property⟩
  have wf := Finite.wellFounded_of_trans_of_irrefl included
  have lift : ∀ vertex : Seen, Acc included vertex → Acc graph.Depends vertex.val := by
    intro vertex accessible
    induction accessible with
    | intro parent _ ih =>
      exact .intro _ fun child step => ih ⟨child, parent.property.tail step⟩ (.single step)
  exact lift ⟨root, .refl⟩ (wf.apply _)

end Silmaril.Proofs.Semantics.Naming
