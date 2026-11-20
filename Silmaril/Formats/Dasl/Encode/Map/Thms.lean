module

public import Silmaril.Formats.Dasl.Encode.Map.Defs
public import Silmaril.Formats.Dasl.Encode.Thms
public import Silmaril.Semantics.OrderedMap.Thms
import Silmaril.Proofs.Formats.Dasl.EncodeMap

public section

namespace Silmaril.Formats.Dasl.Encode

open Silmaril.Semantics

variable {Name Ref Key Item : Type} [LinearOrder Key]

/-- Pick the entry layout independently from key/value representations.
Decoding validates the order of the *decoded* keys. -/
def mapWith (entry : TotalCodec (Tree Ref Name × Tree Ref Name) (Tree Ref Name))
    (key : TotalCodec Key (Tree Ref Name)) (item : TotalCodec Item (Tree Ref Name)) :
    TotalCodec (Semantics.OrderedMap Key Item) (Tree Ref Name) :=
  OrderedMap.entriesCodec.then (listOf ((key.prod item).then entry))

def pairMap (key : TotalCodec Key (Tree Ref Name)) (item : TotalCodec Item (Tree Ref Name)) :
    TotalCodec (Semantics.OrderedMap Key Item) (Tree Ref Name) := mapWith pairEntry key item

def recordMap (key : TotalCodec Key (Tree Ref Name)) (item : TotalCodec Item (Tree Ref Name)) :
    TotalCodec (Semantics.OrderedMap Key Item) (Tree Ref Name) := mapWith recordEntry key item

def setKeys : TotalCodec (OrderedSet Key) (List Key) :=
  ⟨Semantics.OrderedMap.keys, OrderedSet.ofKeys?, Proofs.Formats.Dasl.EncodeMap.keys_roundtrip⟩

def setOf (key : TotalCodec Key (Tree Ref Name)) : TotalCodec (OrderedSet Key) (Tree Ref Name) :=
  setKeys.then (listOf key)

theorem pair_record_distinct (entry : Tree Ref Name × Tree Ref Name) :
    pairEntry.encode entry ≠ recordEntry.encode entry := by
  intro same
  cases same

end Silmaril.Formats.Dasl.Encode
