module

public import Mathlib.Data.Finset.Sort
public import Silmaril.Semantics.OrderedMap.Defs

@[expose] public section

namespace Silmaril.Semantics.OrderedMap

variable {Key Item OtherKey OtherItem : Type} [LinearOrder Key]

/-- The semantic domain of a partial lookup. -/
def support (lookup : Key → Option Item) : Set Key := {key | (lookup key).isSome}

def keySet (map : OrderedMap Key Item) : Finset Key := map.keys.toFinset

/-- Tabulate a lookup on a finite universe, dropping failed lookups. Keys outside
the universe are not queried. Sorting uses the target key order. -/
def ofLookupOn (keys : Finset Key) (lookup : Key → Option Item) : OrderedMap Key Item where
  entries := (keys.sort (· ≤ ·)).filterMap fun key => (lookup key).map (key, ·)
  ordered := List.pairwise_filterMap.mpr <| (Finset.sortedLT_sort keys).pairwise.imp (by
    intro left right lt leftEntry hl rightEntry hr
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hl
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hr; exact lt)

/-- Transport equality along the key equivalence and re-sort in the new order.
The value equivalence is applied only to present values. -/
def transport [LinearOrder OtherKey] (key : Key ≃ OtherKey) (item : Item ≃ OtherItem)
    (map : OrderedMap Key Item) : OrderedMap OtherKey OtherItem :=
  ofLookupOn (map.keySet.map key.toEmbedding) fun other => (map.lookup? (key.symm other)).map item

end Silmaril.Semantics.OrderedMap

namespace Silmaril.Semantics.OrderedSet

variable {Key : Type} [LinearOrder Key]

def ofFinset (keys : Finset Key) : OrderedSet Key where
  entries := (keys.sort (· ≤ ·)).map (·, ())
  ordered := List.pairwise_map.mpr (Finset.sortedLT_sort keys).pairwise

end Silmaril.Semantics.OrderedSet
