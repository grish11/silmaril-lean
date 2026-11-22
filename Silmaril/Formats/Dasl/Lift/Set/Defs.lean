module

public import Silmaril.Formats.Dasl.Encode.Map.Thms
public import Silmaril.Formats.Dasl.Lift.Defs
public import Mathlib.Data.Finset.Sort

@[expose] public section

namespace Silmaril.Formats.Dasl.Lift

open Silmaril.Semantics (OrderedSet OrderedMap)
open Silmaril.Semantics.Naming (Relation)

variable {Key Item : Type} [LinearOrder Key]

/-- Transport a set representation through explicit, recoverable labels. Labels are not CAS names. -/
def codedSet {Surface : Type} (layout : Relation Surface (Finset Key)) (label : Encode.TotalCodec Item Key) :
    Relation Surface (Finset Item) := fun value items => layout value (items.image label.encode)

/-- The generic DASL ordered-set codec, read extensionally as a finite set of keys. -/
def orderedSet (key : Encode.TotalCodec Key Value) : Relation Value (Finset Key) :=
  fun value keys => ∃ set : OrderedSet Key, (Encode.setOf key).encode set = value ∧ set.keys.toFinset = keys

def orderedKeySet (keys : Finset Key) : OrderedSet Key :=
  ⟨keys.sort.map (·, ()), List.pairwise_map.mpr keys.sortedLT_sort.pairwise⟩

end Silmaril.Formats.Dasl.Lift
