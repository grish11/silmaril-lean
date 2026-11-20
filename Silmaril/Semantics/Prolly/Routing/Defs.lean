module

public import Silmaril.Semantics.Prolly.Defs

@[expose] public section

namespace Silmaril.Semantics.Prolly

variable {Key Payload Child : Type}

/-- The first interval with inclusive upper bound at least the query. -/
def selectChild [LinearOrder Key] (key : Key) (children : List (Key × Child)) : Option (Key × Child) :=
  children.find? fun child => decide (key ≤ child.1)

/-- Every branch is nonempty, and each separator is the last leaf key of its subtree. -/
def Node.Separators : (level : Nat) → Node Key Payload level → Prop
  | 0, _ => True
  | level + 1, children => children ≠ [] ∧ ∀ child ∈ children,
      (flatten level child.2).getLast?.map Prod.fst = some child.1 ∧ Node.Separators level child.2

/-- A finite rooted representation for routing. A runtime node check alone does not certify this. -/
def Tree.Routable (tree : Tree Key Payload) [LinearOrder Key] : Prop :=
  tree.entries.Pairwise (fun left right => left.1 < right.1) ∧ Node.Separators tree.level tree.root

end Silmaril.Semantics.Prolly
