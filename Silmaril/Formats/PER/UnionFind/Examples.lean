module

import Silmaril.Formats.PER.UnionFind.Thms

namespace Silmaril.Formats.PER.UnionFindExamples

private def assign : Nat → Option Nat
  | 1 | 2 => some 90
  | 5 => some 91
  | _ => none

example : (PER.fibers assign).rel 1 2 := ⟨90, rfl, rfl⟩

example : ¬ (PER.fibers assign).Dom 90 := by simp [assign]

example : ¬ (PER.fibers assign).Dom 6 := by simp [assign]

example : (PER.fibers (fun key => (assign key).map (· + 10))).classes = (PER.fibers assign).classes :=
  PER.classes_eq_iff.mpr (PER.fibers_relabel assign (· + 10) (fun _ _ hit => Nat.add_right_cancel hit))

example (state merged : PER.UnionFind Nat) (hit : state.union 1 5 = some merged)
    (same : state.partition.rel 1 2) : merged.sameClass 2 5 = some true := by
  apply (merged.sameClass_spec 2 5).1.mpr
  exact (PER.UnionFind.union_rel_iff hit 2 5).mpr
    (Or.inr (Or.inl ⟨state.partition.laws.symm same, (state.union_isSome 1 5).mp (hit ▸ rfl) |>.2⟩))

end Silmaril.Formats.PER.UnionFindExamples
