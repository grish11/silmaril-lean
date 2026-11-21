module

public import Mathlib.Data.List.Basic

/-! A persistent sequence with cached lengths and path-local edits. Shape is
not semantic identity until the sequence is explicitly normalized. -/

@[expose] public section

namespace Silmaril.Semantics.MeasuredSequence

inductive Tree (Item : Type) where
  | empty
  | one (item : Item)
  | branch (length : Nat) (left right : Tree Item)
  deriving DecidableEq

variable {Item : Type}

def size : Tree Item → Nat
  | .empty => 0
  | .one _ => 1
  | .branch length _ _ => length

def flatten : Tree Item → List Item
  | .empty => []
  | .one item => [item]
  | .branch _ left right => flatten left ++ flatten right

def Valid : Tree Item → Prop
  | .empty | .one _ => True
  | .branch length left right =>
    Valid left ∧ Valid right ∧ 0 < size left ∧ 0 < size right ∧ length = size left + size right

def append (left right : Tree Item) : Tree Item :=
  match left, right with
  | .empty, right => right
  | left, .empty => left
  | left, right => .branch (size left + size right) left right

def get? : Tree Item → Nat → Option Item
  | .empty, _ => none
  | .one value, 0 => some value
  | .one _, _ + 1 => none
  | .branch _ left right, index =>
    if index < size left then get? left index else get? right (index - size left)

/-- Set an existing position, leaving an out-of-bounds sequence unchanged. -/
def set : Tree Item → Nat → Item → Tree Item
  | .empty, _, _ => .empty
  | .one _, 0, value => .one value
  | .one old, _ + 1, _ => .one old
  | .branch length left right, index, value =>
    if index < size left then .branch length (set left index value) right
    else .branch length left (set right (index - size left) value)

/-- Split at a prefix length, clipping at the end of the sequence. At a node
boundary, return both original children. -/
def splitAt : Tree Item → Nat → Tree Item × Tree Item
  | .empty, _ => (.empty, .empty)
  | .one value, 0 => (.empty, .one value)
  | .one value, _ + 1 => (.one value, .empty)
  | .branch _ left right, index =>
    if index < size left then
      let parts := splitAt left index
      (parts.1, append parts.2 right)
    else if index = size left then (left, right)
    else
      let parts := splitAt right (index - size left)
      (append left parts.1, parts.2)

/-- Replace up to `count` items at `index`, clipping as for `splitAt`. -/
def splice (tree : Tree Item) (index count : Nat) (inserted : Tree Item) : Tree Item :=
  let parts := splitAt tree index
  let after := (splitAt parts.2 count).2
  append parts.1 (append inserted after)

/-- Build by recursively bisecting at the floor midpoint. Fuel makes the
definition structural; `ofList` supplies sufficient fuel. -/
def build : Nat → List Item → Tree Item
  | 0, _ => .empty
  | _ + 1, [] => .empty
  | _ + 1, [item] => .one item
  | fuel + 1, first :: second :: rest =>
    let items := first :: second :: rest
    let midpoint := items.length / 2
    append (build fuel (items.take midpoint)) (build fuel (items.drop midpoint))

def ofList (items : List Item) : Tree Item := build items.length items

def normalize (tree : Tree Item) : Tree Item := ofList (flatten tree)

def Normal (tree : Tree Item) : Prop := normalize tree = tree

def Bisected : Tree Item → Prop
  | .empty | .one _ => True
  | .branch length left right => size left = length / 2 ∧ Bisected left ∧ Bisected right

end Silmaril.Semantics.MeasuredSequence
