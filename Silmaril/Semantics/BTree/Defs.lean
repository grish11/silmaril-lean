module

public import Silmaril.Semantics.OrderedMap.Defs

/-! A finite leaf-oriented B-tree with inclusive upper dividers. The model
uses logical node positions and has no page addresses or encoding assumptions. -/

@[expose] public section

namespace Silmaril.Semantics.BTree

variable {Key Value Child : Type}

structure Branch (Key Child : Type) where
  fenced : List (Key × Child)
  rightmost : Child

/-- Children in slot order, with the rightmost child at slot `fenced.length`. -/
def Branch.children (branch : Branch Key Child) : List Child :=
  branch.fenced.map Prod.snd ++ [branch.rightmost]

/-- A leaf holds bindings. A branch with `n` dividers has `n + 1` children,
all at the preceding height. The height index enforces a common leaf depth. -/
@[reducible] def Node (Key Value : Type) : Nat → Type
  | 0 => List (Key × Value)
  | height + 1 => Branch Key (Node Key Value height)

structure Tree (Key Value : Type) where
  height : Nat
  root : Node Key Value height

/-- The first child whose upper divider is at least the query, or the
rightmost child. The returned slot is zero based. -/
def Branch.route [LinearOrder Key] (key : Key) (branch : Branch Key Child) : Nat × Child :=
  let slot := branch.fenced.findIdx (fun entry => decide (key ≤ entry.1))
  (slot, (branch.fenced[slot]?.map Prod.snd).getD branch.rightmost)

/-- The leaf bindings in child order. Internal dividers are absent from this view. -/
def Node.entries : (height : Nat) → Node Key Value height → List (Key × Value)
  | 0, node => node
  | height + 1, node => node.fenced.flatMap (fun entry => entries height entry.2) ++
      entries height node.rightmost

def Tree.entries (tree : Tree Key Value) : List (Key × Value) := Node.entries tree.height tree.root

/-- Search follows exactly one child per branch and looks up the query in
its destination leaf using equality. Semantic correctness requires validity. -/
def Node.lookup? [LinearOrder Key] (key : Key) : (height : Nat) → Node Key Value height → Option Value
  | 0, node => node.lookup key
  | height + 1, node => lookup? key height (node.route key).2

def Tree.lookup? [LinearOrder Key] (tree : Tree Key Value) (key : Key) : Option Value :=
  Node.lookup? key tree.height tree.root

/-- The half-open search interval `(lower, upper]`. Absent endpoints are unbounded. -/
def InRange [LinearOrder Key] (lower upper : Option Key) (key : Key) : Prop :=
  (∀ bound, lower = some bound → bound < key) ∧ (∀ bound, upper = some bound → key ≤ bound)

/-- Each divider lies strictly between the inherited endpoints. It is the
inclusive upper bound of its left child and the exclusive lower bound of the
remaining children. The rightmost child inherits the original upper bound. -/
def ValidChildren [LinearOrder Key] (valid : Option Key → Option Key → Child → Prop)
    (upper : Option Key) (rightmost : Child) : Option Key → List (Key × Child) → Prop
  | lower, [] => valid lower upper rightmost
  | lower, (divider, child) :: rest =>
      (∀ bound, lower = some bound → bound < divider) ∧
      (∀ bound, upper = some bound → divider < bound) ∧
      valid lower (some divider) child ∧ ValidChildren valid upper rightmost (some divider) rest

/-- Leaves have strictly increasing keys in their inherited interval.
Branches have at least one divider and satisfy `ValidChildren` recursively. -/
def Node.ValidWithin [LinearOrder Key] :
    (height : Nat) → Option Key → Option Key → Node Key Value height → Prop
  | 0, lower, upper, node =>
      node.Pairwise (fun left right => left.1 < right.1) ∧
      ∀ entry ∈ node, InRange lower upper entry.1
  | height + 1, lower, upper, node =>
      node.fenced ≠ [] ∧ ValidChildren (ValidWithin height) upper node.rightmost lower node.fenced

/-- Height and branch arity are enforced by shape. Validity places no other
occupancy or capacity bounds, allows empty leaves, and permits a divider
above every key in its left child. -/
def Tree.Valid [LinearOrder Key] (tree : Tree Key Value) : Prop :=
  Node.ValidWithin tree.height none none tree.root

end Silmaril.Semantics.BTree
