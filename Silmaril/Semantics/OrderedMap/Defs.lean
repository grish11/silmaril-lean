module

public import Mathlib.Order.Basic

@[expose] public section

namespace Silmaril.Semantics

/-- Finite maps in strictly increasing key order. The order is part of the
encoding choice, and equal keys never have competing entries. -/
@[ext] structure OrderedMap (Key Payload : Type) [LinearOrder Key] where
  entries : List (Key × Payload)
  ordered : entries.Pairwise (fun left right => left.1 < right.1)

namespace OrderedMap

variable {Key Payload : Type} [LinearOrder Key]

def ofEntries? (entries : List (Key × Payload)) : Option (OrderedMap Key Payload) :=
  if ordered : entries.Pairwise (fun left right => left.1 < right.1) then some ⟨entries, ordered⟩ else none

def lookup? (map : OrderedMap Key Payload) (key : Key) : Option Payload := map.entries.lookup key

def keys (map : OrderedMap Key Payload) : List Key := map.entries.map Prod.fst

end OrderedMap

abbrev OrderedSet (Key : Type) [LinearOrder Key] := OrderedMap Key Unit

namespace OrderedSet

variable {Key : Type} [LinearOrder Key]

def ofKeys? (keys : List Key) : Option (OrderedSet Key) := OrderedMap.ofEntries? (keys.map (·, ()))

def contains (set : OrderedSet Key) (key : Key) : Bool := (set.lookup? key).isSome

end OrderedSet
end Silmaril.Semantics
