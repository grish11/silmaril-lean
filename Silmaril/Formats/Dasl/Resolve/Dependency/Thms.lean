module

public import Silmaril.Formats.Dasl.Resolve.Dependency.Defs
public import Silmaril.Formats.Dasl.RawStore.Thms
public import Silmaril.Formats.Dasl.Resolve.View.Thms
public import Silmaril.Semantics.Naming.Dependency.Thms
import Silmaril.Proofs.Formats.Dasl.Dependency

public section

namespace Silmaril.Formats.Dasl

open Silmaril.Semantics.Naming

variable {Name : Type} {store : Store Name} {root : Name}

theorem Store.dependency_depends (store : Store Name) : store.dependency.Depends = Depends store := rfl

theorem Store.dependency_complete_iff : store.dependency.CompleteBelow root ↔
    (∃ source, store.objects root source) ∧ ClosedBelow store root :=
  Proofs.Formats.Dasl.dependency_complete_iff

theorem Shallow.directLinks_finite (tree : Shallow Name) : tree.directLinks.Finite :=
  Proofs.Formats.Dasl.direct_links_finite tree

theorem Store.dependency_finite_branching (bound : store.Binding) (parent : Name) :
    {child | store.dependency.Depends child parent}.Finite :=
  store.dependency.finite_branching bound Proofs.Formats.Dasl.dependency_children_finite parent

theorem Store.dependency_bounded_iff (bound : store.Binding) :
    (∃ fuel, Dependency.Bounded store.dependency.Depends fuel root) ↔ Acc store.dependency.Depends root :=
  Dependency.exists_bounded_iff_acc fun {parent} _ => store.dependency_finite_branching bound parent

theorem full_exists_iff_dependency (bound : store.Binding) :
    (∃ target, FullNames store root target) ↔ Acc store.dependency.Depends root ∧ store.dependency.CompleteBelow root :=
  (full_exists_iff bound root).trans ⟨fun ⟨hit, access, closed⟩ => ⟨access, Store.dependency_complete_iff.mpr ⟨hit, closed⟩⟩,
    fun ⟨access, ready⟩ => let ⟨hit, closed⟩ := Store.dependency_complete_iff.mp ready; ⟨hit, access, closed⟩⟩

/-- No accessibility or completeness hypothesis is needed for a partial result. -/
theorem Reader.observeRoot_sound_in (reader : Reader Name) (included : reader.store.Subset store)
    {fuel : Nat} {result : Partial Name} (found : reader.observeRoot? fuel root = some result) :
    PartialNames store root result :=
  let ⟨hit, objects, blobs⟩ := reader.observeRoot_sound found
  ⟨included.1 hit, fun _ _ entry => included.1 (objects entry), fun _ _ entry => included.2 (blobs entry)⟩

/-- A bounded observation succeeds fully precisely when there is a finite
expansion. A result with unresolved references is not a full embed. -/
theorem Reader.exists_full_observation_iff (reader : Reader Name) :
    (∃ (fuel : Nat) (target : Named Name), reader.observeRoot? fuel root = some target.embed) ↔
      Acc reader.store.dependency.Depends root ∧ reader.store.dependency.CompleteBelow root :=
  Proofs.Formats.Dasl.exists_full_observation_iff reader

theorem RawStore.completion_iff_dependency {decoder : RawStore.Decoder Name}
    {policy base extended : RawStore.Blocks Name} : RawStore.Completes decoder policy base extended root ↔
      Subset base extended ∧ Binding extended ∧ Subset extended policy ∧
        Acc (decoder.view extended).dependency.Depends root ∧ (decoder.view extended).dependency.CompleteBelow root :=
  RawStore.completion_iff.trans <| and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    ⟨fun ⟨hit, access, closed⟩ => ⟨access, Store.dependency_complete_iff.mpr ⟨hit, closed⟩⟩,
     fun ⟨access, ready⟩ => let ⟨hit, closed⟩ := Store.dependency_complete_iff.mp ready; ⟨hit, access, closed⟩⟩

end Silmaril.Formats.Dasl
