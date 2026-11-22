module

public import Silmaril.Formats.PER.Partition.Operations.Defs
public import Silmaril.Formats.PER.UnionFind.Thms

public section

namespace Silmaril.Proofs.Formats.PERPartitionOperations

open Silmaril.Formats PER Partition Silmaril.Semantics

variable {Key : Type}

theorem union_join [LinearOrder Key] {state result : UnionFind Key} {left right : Key}
    (hit : state.union left right = some result) :
    result.partition = join state.partition (identify left right) := by
  have supported := (state.union_isSome left right).mp (hit ▸ rfl)
  have selected : result.partition.rel left right :=
    (UnionFind.union_rel_iff hit left right).mpr (.inr (.inl supported))
  apply le_antisymm
  · intro first second pair upper
    have edge := upper.property.2 (show (identify left right).rel left right from ⟨Or.inl rfl, Or.inr rfl, trivial⟩)
    rcases (UnionFind.union_rel_iff hit first second).mp pair with old | ⟨hl, hr⟩ | ⟨hr, hl⟩
    · exact upper.property.1 old
    · exact upper.val.laws.trans (upper.property.1 hl) (upper.val.laws.trans edge (upper.val.laws.symm (upper.property.1 hr)))
    · exact upper.val.laws.trans (upper.property.1 hr) (upper.val.laws.trans (upper.val.laws.symm edge) (upper.val.laws.symm (upper.property.1 hl)))
  · have includes : state.partition ≤ result.partition :=
      fun first second old => (UnionFind.union_rel_iff hit first second).mpr (.inl old)
    have identifies : identify left right ≤ result.partition := by
      rintro _ _ ⟨rfl | rfl, rfl | rfl, _⟩
      · exact result.partition.dom_left selected
      · exact selected
      · exact result.partition.laws.symm selected
      · exact result.partition.dom_right selected
    exact fun _ _ joined => joined ⟨result.partition, includes, identifies⟩

theorem tabulate_exact [LinearOrder Key] (keys : Finset Key) (lookup : PartialMap Key) :
    (tabulate keys lookup).lookup? = lookup ↔ ∀ key, (lookup key).isSome → key ∈ keys := by
  constructor
  · intro equal key known
    have result := congrFun equal key
    rw [OrderedMap.lookup_ofLookupOn] at result
    by_contra missing
    simp [missing] at result
    simp [← result] at known
  · intro covers
    funext key
    rw [OrderedMap.lookup_ofLookupOn]
    cases hit : lookup key with
    | none => simp
    | some _ => exact ite_eq_left (covers key (by simp [hit]))

theorem join_dom (left right : PER Key) (key : Key) : (join left right).Dom key ↔ left.Dom key ∨ right.Dom key := by
  constructor
  · intro related
    let upper := (PER.universal Key).restrict (fun value => left.Dom value ∨ right.Dom value)
    have hl : left ≤ upper := fun _ _ h => ⟨Or.inl (left.dom_left h), Or.inl (left.dom_right h), trivial⟩
    have hr : right ≤ upper := fun _ _ h => ⟨Or.inr (right.dom_left h), Or.inr (right.dom_right h), trivial⟩
    exact (related ⟨upper, hl, hr⟩).1
  · rintro (known | known) ⟨_, hl, hr⟩
    · exact hl known
    · exact hr known

theorem restrict_partition [LinearOrder Key] (labels : FiniteMap Key) (selected : Finset Key) :
    fibers (restrictMap labels selected).lookup? = (fibers labels.lookup?).restrict (· ∈ selected) := by
  apply PER.ext
  intro left right
  change (∃ label, _ = some label ∧ _ = some label) ↔ left ∈ selected ∧ right ∈ selected ∧ _
  simp only [restrictMap, OrderedMap.lookup_ofLookupOn]
  by_cases hl : left ∈ selected <;> by_cases hr : right ∈ selected <;> simp [hl, hr]
  rfl

theorem finite_join [LinearOrder Key] (left right : FiniteMap Key) :
    ∃ labels : FiniteMap Key, fibers labels.lookup? = join (fibers left.lookup?) (fibers right.lookup?) := by
  apply (Partition.finite_support_iff _).mp
  have support : {key | (join (fibers left.lookup?) (fibers right.lookup?)).Dom key} =
      (left.keySet : Set Key) ∪ (right.keySet : Set Key) :=
    Set.ext fun key => (join_dom _ _ _).trans (or_congr (map_dom_iff_key left key) (map_dom_iff_key right key))
  rw [support]
  exact left.keySet.finite_toSet.union right.keySet.finite_toSet

end Silmaril.Proofs.Formats.PERPartitionOperations
