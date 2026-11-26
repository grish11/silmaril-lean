module

import Silmaril.Semantics.BTree.Thms
import Mathlib.Data.Nat.Basic

namespace Silmaril.Semantics.BTree

private def left : Node Nat String 1 :=
  ⟨[(4, [(2, "two"), (4, "four")]), (8, [(6, "six")])], [(10, "ten")]⟩

private def right : Node Nat String 1 :=
  ⟨[(20, [(13, "thirteen"), (20, "twenty")])], [(24, "twenty-four")]⟩

private def sample : Tree Nat String := ⟨2, ⟨[(12, left)], right⟩⟩

private theorem sample_valid : sample.Valid := by
  simp [sample, left, right, Tree.Valid, Node.ValidWithin, ValidChildren, InRange, List.pairwise_cons]

-- Equality at a divider stays on its left. The second divider selects slot one.
example : (left.route 4).1 = 0 := rfl
example : (left.route 6).1 = 1 := rfl
example : (left.route 10).1 = 2 := rfl

example : sample.lookup? 4 = some "four" := rfl
example : sample.lookup? 6 = some "six" := rfl
example : sample.lookup? 24 = some "twenty-four" := rfl
example : sample.lookup? 12 = none := rfl

example : (6, "six") ∈ sample.entries := (sample.lookup_eq_some_iff sample_valid).mp rfl
example : sample.lookup? 10 = (sample.toOrderedMap sample_valid).lookup? 10 :=
  sample.lookup_eq_orderedMap sample_valid 10

private def emptyTree : Tree Nat String := ⟨0, []⟩
example : emptyTree.Valid := by simp [emptyTree, Tree.Valid, Node.ValidWithin]
example : emptyTree.lookup? 4 = none := rfl

-- A right child cannot contain its exclusive lower divider, even with ordered leaves.
private def misplaced : Tree Nat String := ⟨1, ⟨[(4, [(2, "two")])], [(4, "four")]⟩⟩
example : ¬ misplaced.Valid := by
  simp [misplaced, Tree.Valid, Node.ValidWithin, ValidChildren, InRange]

end Silmaril.Semantics.BTree
