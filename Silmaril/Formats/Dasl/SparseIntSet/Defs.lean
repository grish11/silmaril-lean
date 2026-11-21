module

public import Mathlib.Data.Finset.Sort
public import Silmaril.Formats.Dasl.Encode.Map.Thms

@[expose] public section

namespace Silmaril.Formats.Dasl.SparseIntSet

open Silmaril.Semantics

/-- Signed rather than unsigned-bit order, kept local to this layout. -/
abbrev signedOrder : LinearOrder Int64 := LinearOrder.lift' Int64.toInt (fun _ _ same => Int64.toInt.inj same)

attribute [local instance] signedOrder

abbrev Layout := OrderedSet Int64

instance : DecidableEq Layout := fun left right =>
  decidable_of_iff (left.entries = right.entries) ⟨OrderedMap.ext, congrArg OrderedMap.entries⟩

def keys (layout : Layout) : List Int64 := layout.keys

def fromKeys? (keys : List Int64) : Option Layout := OrderedSet.ofKeys? keys

def members (layout : Layout) : Finset Int64 := layout.keys.toFinset

def ofFinset (values : Finset Int64) : Layout where
  entries := (values.sort signedOrder.le).map (·, ())
  ordered := List.pairwise_map.mpr (Finset.sortedLT_sort values).pairwise

/-- Normalize arbitrary order and duplicates; the wire decoder instead rejects them. -/
def normalize (values : List Int64) : Layout := ofFinset values.toFinset

def contains (layout : Layout) (value : Int64) : Bool := decide (value ∈ layout.keys)

def cardinality (layout : Layout) : Nat := layout.keys.length

/-- One shallow object: a list with one signed i64 per member, no child blocks. -/
def codec {Name : Type} : Encode.TotalCodec Layout (Shallow Name) := Encode.setOf Encode.signed

end Silmaril.Formats.Dasl.SparseIntSet
