module

import Silmaril.Formats.Dasl.Resolve.Dependency.Thms

namespace Silmaril.Formats.Dasl

open Silmaril.Semantics.Naming

private def chain : Reader Nat := ⟨fun name => some (.ref (.obj (name + 1))), fun _ => none⟩

private theorem successor_edge {child parent : Nat} : chain.store.dependency.Depends child parent ↔ child = parent + 1 := by
  constructor
  · rintro ⟨source, hit, linked⟩
    cases Option.some.inj hit
    change Link.obj child ∈ ({Link.obj (parent + 1)} : Set (Link Nat)) at linked
    exact Link.obj.inj (Set.mem_singleton_iff.mp linked)
  · rintro rfl
    exact ⟨_, rfl, rfl⟩

private theorem increases {child parent : Nat} (path : Relation.TransGen chain.store.dependency.Depends child parent) :
    parent < child := by
  induction path with
  | single step => exact (successor_edge.mp step).symm ▸ Nat.lt_succ_self _
  | tail _ step ih => exact Nat.lt_trans ((successor_edge.mp step).symm ▸ Nat.lt_succ_self _) ih

private theorem no_access {name : Nat} (access : Acc chain.store.dependency.Depends name) : False := by
  induction access with
  | intro name _ ih => exact ih (name + 1) (successor_edge.mpr rfl)

example : chain.store.dependency.AcyclicBelow 0 := fun {_} _ cycle => Nat.lt_irrefl _ (increases cycle)

example (parent : Nat) : {child | chain.store.dependency.Depends child parent}.Finite :=
  Store.dependency_finite_branching chain.binding parent

example : chain.store.dependency.CompleteBelow 0 := by
  refine ⟨⟨_, rfl⟩, ?_⟩
  rintro parent (child | blob) _ ⟨source, hit, linked⟩
  · exact ⟨_, rfl⟩
  · cases Option.some.inj hit
    change Link.blob blob ∈ ({Link.obj (parent + 1)} : Set (Link Nat)) at linked
    cases Set.mem_singleton_iff.mp linked

example : ¬ ∃ (fuel : Nat) (target : Named Nat), chain.observeRoot? fuel 0 = some target.embed :=
  fun success => no_access (chain.exists_full_observation_iff.mp success).1

example : PartialNames chain.store 0 (.obj 1 (.ref (.obj 2))) :=
  chain.observeRoot_sound (fuel := 1) rfl

private def terminal : Reader Unit := ⟨fun _ => some (.ref (.blob ())), fun _ => some ByteArray.empty⟩

example : Dependency.Bounded terminal.store.dependency.Depends 0 () := by
  rintro _ ⟨source, hit, linked⟩
  cases Option.some.inj hit
  change Link.obj () ∈ ({Link.blob ()} : Set (Link Unit)) at linked
  cases Set.mem_singleton_iff.mp linked

example : terminal.observeRoot? 1 () = some (Named.embed (.blob () ByteArray.empty)) := rfl

end Silmaril.Formats.Dasl
