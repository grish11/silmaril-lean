module

public import Silmaril.Formats.Dasl.Encode.Partition.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl.EncodePartition

open Silmaril.Formats.Dasl.Encode.Partition Silmaril.Semantics

variable {Key : Type} [LinearOrder Key]

theorem group_member (labels : OrderedMap Key Key) (key label : Key) :
    (∃ members, (label, members) ∈ (group labels).entries ∧ key ∈ members) ↔ labels.lookup? key = some label := by
  simp only [← OrderedMap.lookup_eq_some_iff, group, OrderedMap.lookup_ofLookupOn]
  constructor
  · rintro ⟨members, lookup, mem⟩
    split at lookup
    · rw [← Option.some.inj lookup] at mem
      exact (Finset.mem_filter.mp mem).2
    · cases lookup
  · intro hit
    have labelMem : label ∈ (labels.entries.map Prod.snd).toFinset :=
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨(key, label), labels.lookup_eq_some_iff.mp hit, rfl⟩)
    have member : key ∈ labels.keySet := (labels.mem_keySet key).mpr (by simp [hit])
    exact ⟨_, ite_eq_left labelMem, Finset.mem_filter.mpr ⟨member, hit⟩⟩

theorem ungroup_group (labels : OrderedMap Key Key) : ungroup (group labels) = labels := by
  apply OrderedMap.eq_of_lookup
  intro key
  apply Option.ext
  intro label
  rw [ungroup, OrderedMap.lookup_ofLookupOn]
  let pick := fun entry : Key × Finset Key => if key ∈ entry.2 then some entry.1 else none
  have sound {root : Key} (hit : (group labels).entries.findSome? pick = some root) :
      labels.lookup? key = some root := by
    obtain ⟨⟨candidate, members⟩, candidateMem, found⟩ := List.exists_of_findSome?_eq_some hit
    change (if key ∈ members then some candidate else none) = some root at found
    split at found
    · obtain rfl := Option.some.inj found
      exact (group_member labels key candidate).mp ⟨members, candidateMem, ‹key ∈ members›⟩
    · cases found
  constructor
  · intro hit
    split at hit
    · exact sound hit
    · cases hit
  · intro hit
    obtain ⟨members, groupMem, belongs⟩ := (group_member labels key label).mpr hit
    have known : key ∈ ((group labels).entries.flatMap fun entry => entry.2.sort (· ≤ ·)).toFinset :=
      List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨(label, members), groupMem, (Finset.mem_sort _).mpr belongs⟩)
    rw [ite_eq_left known]
    cases found : (group labels).entries.findSome? pick with
    | none =>
      have missing := (List.findSome?_eq_none_iff.mp found) (label, members) groupMem
      simp [pick, belongs] at missing
    | some root => exact congrArg some (Option.some.inj ((sound found).symm.trans hit))

theorem ungroup?_spec (groups : ClassMembers Key) (labels : OrderedMap Key Key) :
    ungroup? groups = some labels ↔ group labels = groups := by
  constructor
  · unfold ungroup?
    dsimp only
    intro hit
    split at hit
    · cases Option.some.inj hit
      exact OrderedMap.ext ‹_›
    · cases hit
  · intro same
    rw [← same]
    simp [ungroup?, ungroup_group]

end Silmaril.Proofs.Formats.Dasl.EncodePartition
