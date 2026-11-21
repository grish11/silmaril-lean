module

import Silmaril.Semantics.Prolly.Cuts.Thms

open Silmaril.Semantics Silmaril.Semantics.Prolly

private def policy : Policy Nat := ⟨3, by decide, fun _ key => key % 2 == 0⟩

private def keys : List Nat := [1, 2, 4, 6, 7, 8, 9]

example : CutPartition (policy.cut 0) [[1, 2], [4, 6], [7, 8], [9]] :=
  ((chunk_eq_iff (policy.cut 0) (items := keys)).mp (by decide)).2

example : ¬ CutPartition (policy.cut 0) [[1, 2, 4], [6, 7, 8], [9]] := by
  intro delayed
  have actual := (chunk_eq_iff (policy.cut 0) (items := keys)).mpr ⟨rfl, delayed⟩
  exact (by decide : chunk (policy.cut 0) keys ≠ [[1, 2, 4], [6, 7, 8], [9]]) actual

private def entries : OrderedMap Nat Nat :=
  ⟨[(1, 0), (2, 0), (4, 0), (6, 0), (7, 0), (8, 0), (9, 0)], by decide⟩

example : (build policy entries).level = 2 := by decide

example {tree : Tree Nat Nat} (canonical : CanonicalGrowth policy 0 entries.entries tree) :
    tree = build policy entries := canonical.unique (build_canonical policy entries)
