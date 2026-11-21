module

public import Silmaril.Formats.Dasl.Resolve.Dependency.Defs
public import Silmaril.Formats.Dasl.Resolve.View.Thms
public import Silmaril.Formats.Dasl.Named.Thms
public import Silmaril.Semantics.Naming.Dependency.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl

open Silmaril.Formats.Dasl Silmaril.Semantics.Naming

variable {Name : Type} {store : Store Name} {root : Name}

theorem dependency_complete_iff : store.dependency.CompleteBelow root ↔
    (∃ source, store.objects root source) ∧ ClosedBelow store root := by
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · intro ready parent source path hit
    exact ⟨fun child linked => ready (child := .inl child) path ⟨source, hit, linked⟩,
      fun child linked => ready (child := .inr child) path ⟨source, hit, linked⟩⟩
  · rintro closed parent (child | child) path ⟨source, hit, linked⟩
    · exact (closed path hit).1 child linked
    · exact (closed path hit).2 child linked

theorem direct_links_finite (tree : Shallow Name) : tree.directLinks.Finite := by
  induction tree with
  | ref link => exact Set.finite_singleton link
  | obj impossible _ _ | blob impossible _ => exact impossible.elim
  | dict _ children ih | list _ children ih =>
    refine (Set.finite_iUnion ih).subset ?_
    intro link linked
    change ∃ index, link ∈ Shallow.directLinks (children index) at linked
    exact Set.mem_iUnion.mpr linked
  | _ => exact Set.finite_empty

theorem dependency_children_finite (tree : Shallow Name) : (store.dependency.children tree).Finite := by
  apply (direct_links_finite tree).preimage
  apply Function.Injective.injOn
  intro left right equal
  cases left <;> cases right <;> cases equal <;> rfl

theorem exists_full_observation_iff (reader : Reader Name) :
    (∃ (fuel : Nat) (target : Named Name), reader.observeRoot? fuel root = some target.embed) ↔
      Acc reader.store.dependency.Depends root ∧ reader.store.dependency.CompleteBelow root := by
  have full : (∃ (fuel : Nat) (target : Named Name), reader.observeRoot? fuel root = some target.embed) ↔
      ∃ target, FullNames reader.store root target := by
    constructor
    · rintro ⟨_, target, observed⟩
      obtain ⟨hit, admitted⟩ := reader.observeRoot_sound observed
      exact ⟨target, _, hit, Named.admitted_iff_expands.mp admitted⟩
    · rintro ⟨target, expanded⟩
      obtain ⟨fuel, ready⟩ := reader.observeRoot_eventually expanded
      exact ⟨fuel, target, ready fuel le_rfl⟩
  apply full.trans ((full_exists_iff reader.binding root).trans ?_)
  exact ⟨fun ⟨hit, access, complete⟩ => ⟨access, dependency_complete_iff.mpr ⟨hit, complete⟩⟩,
    fun ⟨access, ready⟩ => let ⟨hit, closed⟩ := dependency_complete_iff.mp ready; ⟨hit, access, closed⟩⟩

end Silmaril.Proofs.Formats.Dasl
