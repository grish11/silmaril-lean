module

public import Mathlib.Data.List.SplitLengths

@[expose] public section

namespace Silmaril.Semantics.Rope

variable {Cell : Type}

/-- Mutation-oriented shape; the same sequence can have many raw trees. -/
inductive Tree (Cell : Type) where
  | empty
  | leaf (page : List Cell)
  | branch (count : Nat) (children : Fin count → Tree Cell)

def Tree.ofChildren (children : List (Tree Cell)) : Tree Cell :=
  .branch children.length (fun index => children[index.val])

def Tree.concat (left right : Tree Cell) : Tree Cell := .ofChildren [left, right]

def Tree.pages : Tree Cell → List (List Cell)
  | .empty => []
  | .leaf page => [page]
  | .branch count children => (List.ofFn (n := count) fun index => (children index).pages).flatten

def Tree.flatten (tree : Tree Cell) : List Cell := tree.pages.flatten

def Tree.size (tree : Tree Cell) : Nat := (tree.pages.map List.length).sum

def Tree.depth : Tree Cell → Nat
  | .empty | .leaf _ => 0
  | .branch count children => 1 + (List.ofFn (n := count) fun index => (children index).depth).foldr max 0

def Tree.WidthBound (limit : Nat) : Tree Cell → Prop
  | .empty | .leaf _ => True
  | .branch count children => 0 < count ∧ count ≤ limit ∧ ∀ index, (children index).WidthBound limit

def Tree.AtLevel : Tree Cell → Nat → Prop
  | .empty, level | .leaf _, level => level = 0
  | .branch _ _, 0 => False
  | .branch _ children, level + 1 => ∀ index, (children index).AtLevel level

inductive Bias where
  | left
  | right

structure Geometry where
  pageSize : Nat
  positive : 0 < pageSize
  exponent : Nat
  bias : Bias

def Geometry.fanout (geometry : Geometry) : Nat := 2 ^ (geometry.exponent + 1)

/-- Full groups at the chosen side, and no empty residual group. -/
def sizes (bias : Bias) (capacity count : Nat) : List Nat :=
  let full := List.replicate (count / capacity) capacity
  let rest := if count % capacity = 0 then [] else [count % capacity]
  match bias with
  | .left => full ++ rest
  | .right => rest ++ full

/-- Full payload pages followed by a trailing subpage, if needed. Bias applies
to grouping vertices, not to the payload split. -/
def Geometry.pages (geometry : Geometry) (cells : List Cell) : List (List Cell) :=
  (sizes .left geometry.pageSize cells.length).splitLengths cells

def parentLayer (geometry : Geometry) (nodes : List (Tree Cell)) : List (Tree Cell) :=
  ((sizes geometry.bias geometry.fanout nodes.length).splitLengths nodes).map Tree.ofChildren

def assemble (geometry : Geometry) : Nat → List (Tree Cell) → Tree Cell
  | _, [] => .empty
  | _, [node] => node
  | 0, first :: second :: rest => .ofChildren (first :: second :: rest)
  | fuel + 1, first :: second :: rest => assemble geometry fuel (parentLayer geometry (first :: second :: rest))

def fromList (geometry : Geometry) (cells : List Cell) : Tree Cell :=
  let pages := geometry.pages cells
  assemble geometry pages.length (pages.map Tree.leaf)

def normalize (geometry : Geometry) (source : Tree Cell) : Tree Cell := fromList geometry source.flatten

def Normal (geometry : Geometry) (tree : Tree Cell) : Prop := normalize geometry tree = tree

def ofBytes (geometry : Geometry) (bytes : ByteArray) : Tree UInt8 := fromList geometry bytes.data.toList

def toBytes (rope : Tree UInt8) : ByteArray := ⟨rope.flatten.toArray⟩

/-- Text pages count `Char` values, not UTF-8 bytes or grapheme clusters. -/
def ofString (geometry : Geometry) (text : String) : Tree Char := fromList geometry text.toList

def toString (rope : Tree Char) : String := String.ofList rope.flatten

end Silmaril.Semantics.Rope
