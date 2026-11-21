module

public import Silmaril.Formats.PER.Fibers.Defs
public import Silmaril.Semantics.OrderedMap.Finite.Defs

@[expose] public section

namespace Silmaril.Formats.PER

open Silmaril.Semantics

variable {Key : Type}

/-- Every successful label names a known fixed point. As a parent map this
is already flat: every non-root edge goes directly to a self-root. -/
def Rooted (label : Key → Option Key) : Prop :=
  ∀ ⦃member root⦄, label member = some root → label root = some root

/-- Executable, finite disjoint sets stored as a flat representative map.
This invariant is *not* required to interpret an arbitrary label map as fibers. -/
structure UnionFind (Key : Type) [LinearOrder Key] where
  labels : OrderedMap Key Key
  rooted : Rooted labels.lookup?

namespace UnionFind

variable [LinearOrder Key]

def find (state : UnionFind Key) : Key → Option Key := state.labels.lookup?

def partition (state : UnionFind Key) : PER Key := fibers state.find

def empty : UnionFind Key := ⟨⟨[], .nil⟩, by intro _ _ hit; cases hit⟩

/-- `none` means at least one key is unknown; `some false` means both are
known and belong to different classes. -/
def sameClass (state : UnionFind Key) (left right : Key) : Option Bool := do
  let leftRoot ← state.find left
  let rightRoot ← state.find right
  return decide (leftRoot = rightRoot)

def insertLabels (labels : OrderedMap Key Key) (key : Key) : OrderedMap Key Key :=
  OrderedMap.ofLookupOn (insert key labels.keySet) fun member =>
    if member = key then some key else labels.lookup? member

def redirect (keep drop root : Key) : Key := if root = drop then keep else root

/-- A single pass over the ordered entries; only values change. -/
def mergeLabels (labels : OrderedMap Key Key) (keep drop : Key) : OrderedMap Key Key where
  entries := labels.entries.map fun (member, root) => (member, redirect keep drop root)
  ordered := List.pairwise_map.mpr labels.ordered

end UnionFind
end Silmaril.Formats.PER
