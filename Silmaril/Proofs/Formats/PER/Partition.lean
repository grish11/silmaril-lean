module

public import Silmaril.Formats.PER.Partition.Defs

public section

namespace Silmaril.Proofs.Formats.PERPartition

open Silmaril.Formats PER Silmaril.Semantics Partition

variable {Key : Type} [LinearOrder Key]

theorem least_spec (keys : Finset Key) (relation : PER Key) [DecidableRel relation.rel] (key root : Key) :
    least? keys relation key = some root ↔
      root ∈ keys ∧ relation.rel key root ∧ ∀ other ∈ keys, relation.rel key other → root ≤ other := by
  unfold least?
  dsimp only
  let members := keys.filter (relation.rel key)
  constructor
  · intro hit
    split at hit
    · obtain rfl := Option.some.inj hit
      have present : members.min' ‹members.Nonempty› ∈ members := Finset.min'_mem _ _
      obtain ⟨mem, related⟩ := Finset.mem_filter.mp present
      exact ⟨mem, related, fun other hmem hrel => Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hmem, hrel⟩)⟩
    · cases hit
  · rintro ⟨mem, related, smallest⟩
    have present : root ∈ members := Finset.mem_filter.mpr ⟨mem, related⟩
    have nonempty : members.Nonempty := ⟨root, present⟩
    rw [dite_eq_left nonempty]
    obtain ⟨hmem, hrel⟩ := Finset.mem_filter.mp (Finset.min'_mem members nonempty)
    exact congrArg some (le_antisymm (Finset.min'_le _ _ present) (smallest _ hmem hrel))

theorem canonical_lookup (keys : Finset Key) (relation : PER Key) [DecidableRel relation.rel]
    (covers : ∀ key, relation.Dom key → key ∈ keys) (key : Key) :
    (canonicalOn keys relation).lookup? key = least? keys relation key := by
  rw [canonicalOn, OrderedMap.lookup_ofLookupOn]
  by_cases mem : key ∈ keys
  · exact ite_eq_left mem
  · rw [ite_eq_right mem]
    cases hit : least? keys relation key with
    | none => rfl
    | some root => exact (mem (covers key (relation.dom_left ((least_spec keys relation key root).mp hit).2.1))).elim

theorem canonical_lookup_spec (keys : Finset Key) (relation : PER Key) [DecidableRel relation.rel]
    (covers : ∀ key, relation.Dom key → key ∈ keys) (key root : Key) :
    (canonicalOn keys relation).lookup? key = some root ↔
      relation.rel key root ∧ ∀ other, relation.rel key other → root ≤ other := by
  rw [canonical_lookup keys relation covers, least_spec]
  constructor
  · exact fun ⟨_, related, least⟩ => ⟨related, fun other hit => least other (covers other (relation.dom_right hit)) hit⟩
  · exact fun ⟨related, least⟩ => ⟨covers root (relation.dom_right related), related, fun other _ => least other⟩

theorem canonical_partition (keys : Finset Key) (relation : PER Key) [DecidableRel relation.rel]
    (covers : ∀ key, relation.Dom key → key ∈ keys) : fibers (canonicalOn keys relation).lookup? = relation := by
  apply PER.ext
  intro left right
  change (∃ root, _ = some root ∧ _ = some root) ↔ _
  simp only [canonical_lookup_spec keys relation covers]
  constructor
  · rintro ⟨root, ⟨first, _⟩, ⟨second, _⟩⟩
    exact relation.laws.trans first (relation.laws.symm second)
  · intro related
    have member : ∀ other, relation.rel left other ↔ relation.rel right other := fun _ =>
      ⟨relation.laws.trans (relation.laws.symm related), relation.laws.trans related⟩
    let group := keys.filter (relation.rel left)
    have nonempty : group.Nonempty := ⟨right, Finset.mem_filter.mpr ⟨covers right (relation.dom_right related), related⟩⟩
    let root := group.min' nonempty
    have hroot : relation.rel left root := (Finset.mem_filter.mp (Finset.min'_mem group nonempty)).2
    have least (other : Key) (hit : relation.rel left other) : root ≤ other :=
      Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨covers other (relation.dom_right hit), hit⟩)
    exact ⟨root, ⟨hroot, least⟩, ⟨(member root).mp hroot, fun other hit => least other ((member other).mpr hit)⟩⟩

theorem finite_support_iff (relation : PER Key) :
    ({key | relation.Dom key} : Set Key).Finite ↔
      ∃ labels : OrderedMap Key Key, fibers labels.lookup? = relation := by
  constructor
  · classical
    intro finite
    have covers (key : Key) (present : relation.Dom key) : key ∈ finite.toFinset :=
      finite.mem_toFinset.mpr present
    exact ⟨canonicalOn finite.toFinset relation, canonical_partition finite.toFinset relation covers⟩
  · rintro ⟨labels, rfl⟩
    have equal : {key | (fibers labels.lookup?).Dom key} = (labels.keySet : Set Key) :=
      Set.ext fun key => (fibers_dom labels.lookup? key).trans (labels.mem_keySet key).symm
    exact equal ▸ labels.keySet.finite_toSet

end Silmaril.Proofs.Formats.PERPartition
