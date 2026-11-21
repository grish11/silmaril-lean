module

import Silmaril.Formats.Dasl.Encode.Partition.Thms
import Silmaril.Formats.PER.UnionFind.Thms

namespace Silmaril.Formats.Dasl.Encode.PartitionExamples

open Silmaril.Semantics

private def keys : Finset Nat := {1, 2, 5}

private def ticket (key : Nat) : Option Nat := if key = 5 then some 91 else some 90

private def firstLabels : OrderedMap Nat Nat := OrderedMap.ofLookupOn keys ticket

private def otherLabels : OrderedMap Nat Nat := OrderedMap.ofLookupOn keys (fun key => (ticket key).map (· + 10))

private theorem samePartition : PER.fibers firstLabels.lookup? = PER.fibers otherLabels.lookup? := by
  have transport : otherLabels.lookup? = fun key => (firstLabels.lookup? key).map (· + 10) :=
    funext fun key => by by_cases mem : key ∈ keys <;> simp [firstLabels, otherLabels, mem]
  rw [transport]
  exact (PER.fibers_relabel _ (· + 10) (fun _ _ hit => Nat.add_right_cancel hit)).symm

example : Partition.encodeCanonical Partition.classMembersLayout firstLabels =
    Partition.encodeCanonical Partition.classMembersLayout otherLabels :=
  (Partition.encodeCanonical_eq_iff _ _ _).mpr (PER.classes_eq_iff.mpr samePartition)

example : ¬ (PER.fibers firstLabels.lookup?).Dom 90 := by
  simp [firstLabels, keys]

example (state merged : PER.UnionFind Nat) (hit : state.union 2 5 = some merged) :
    Partition.decodePartition Partition.classMembersLayout (Partition.encodeCanonical Partition.classMembersLayout merged.labels) =
      some merged.partition ∧ merged.partition.rel 2 5 := by
  refine ⟨Partition.decodeCanonical _ _, (PER.UnionFind.union_rel_iff hit 2 5).mpr ?_⟩
  exact Or.inr (Or.inl ((state.union_isSome 2 5).mp (hit ▸ rfl)))

end Silmaril.Formats.Dasl.Encode.PartitionExamples
