module

public import Silmaril.Semantics.BTree.Defs
public import Silmaril.Semantics.OrderedMap.Thms
import Silmaril.Proofs.Semantics.BTree.Lookup

public section

namespace Silmaril.Semantics.BTree

variable {Key Value Child : Type} [LinearOrder Key]

/-- The reported slot selects the reported child, including at the right edge. -/
theorem Branch.route_get (key : Key) (branch : Branch Key Child) :
    branch.children[(branch.route key).1]? = some (branch.route key).2 :=
  Proofs.Semantics.BTree.route_get key branch

/-- The in-order leaf bindings have strictly increasing, hence unique, keys. -/
theorem Node.entries_ordered {height : Nat} {lower upper : Option Key} {node : Node Key Value height}
    (ok : Node.ValidWithin height lower upper node) :
    (Node.entries height node).Pairwise (fun left right => left.1 < right.1) :=
  Proofs.Semantics.BTree.entries_ordered ok

/-- Every binding below a valid node lies in its inherited interval. -/
theorem Node.entries_inRange {height : Nat} {lower upper : Option Key} {node : Node Key Value height}
    (ok : Node.ValidWithin height lower upper node) {entry : Key × Value}
    (present : entry ∈ Node.entries height node) : InRange lower upper entry.1 :=
  Proofs.Semantics.BTree.entries_inRange ok present

/-- Routed lookup agrees with the full leaf sequence, even for queries outside
this node's interval. -/
theorem Node.lookup_eq_entries {height : Nat} {lower upper : Option Key} {node : Node Key Value height}
    (ok : Node.ValidWithin height lower upper node) (key : Key) :
    Node.lookup? key height node = (Node.entries height node).lookup key :=
  Proofs.Semantics.BTree.lookup_eq_entries ok key

/-- The abstract contents of a valid tree as the existing ordered finite map. -/
@[expose] def Tree.toOrderedMap (tree : Tree Key Value) (ok : tree.Valid) : OrderedMap Key Value :=
  ⟨tree.entries, Node.entries_ordered ok⟩

theorem Tree.lookup_eq_orderedMap {tree : Tree Key Value} (ok : tree.Valid) (key : Key) :
    tree.lookup? key = (tree.toOrderedMap ok).lookup? key :=
  Node.lookup_eq_entries ok key

theorem Tree.lookup_eq_some_iff {tree : Tree Key Value} (ok : tree.Valid) {key : Key} {value : Value} :
    tree.lookup? key = some value ↔ (key, value) ∈ tree.entries := by
  rw [tree.lookup_eq_orderedMap ok]
  exact (tree.toOrderedMap ok).lookup_eq_some_iff

theorem Tree.lookup_eq_none_iff {tree : Tree Key Value} (ok : tree.Valid) {key : Key} :
    tree.lookup? key = none ↔ ∀ entry ∈ tree.entries, key ≠ entry.1 := by
  change Node.lookup? key tree.height tree.root = none ↔ _
  rw [Node.lookup_eq_entries ok, List.lookup_eq_none_iff]
  simp [Tree.entries, bne]

end Silmaril.Semantics.BTree
