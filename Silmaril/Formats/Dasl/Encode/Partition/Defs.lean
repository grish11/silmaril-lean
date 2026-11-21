module

public import Silmaril.Formats.Dasl.Encode.Collection.Defs
public import Silmaril.Formats.PER.Partition.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Encode.Partition

open Silmaril.Semantics

variable {Key Name Ref Target : Type} [LinearOrder Key]

/-- A map from class identifiers to their explicit member sets. The raw
layout does not require the identifier to belong to the class. -/
abbrev ClassMembers (Key : Type) [LinearOrder Key] := OrderedMap Key (Finset Key)

def group (labels : OrderedMap Key Key) : ClassMembers Key :=
  OrderedMap.ofLookupOn (labels.entries.map Prod.snd).toFinset fun label =>
    some (labels.keySet.filter fun key => labels.lookup? key = some label)

def ungroup (groups : ClassMembers Key) : OrderedMap Key Key :=
  OrderedMap.ofLookupOn (groups.entries.flatMap fun entry => entry.2.sort (· ≤ ·)).toFinset fun key =>
    groups.entries.findSome? fun entry => if key ∈ entry.2 then some entry.1 else none

/-- Validate the whole layout instead of trusting the first matching group:
empty classes or competing memberships are rejected. -/
def ungroup? (groups : ClassMembers Key) : Option (OrderedMap Key Key) :=
  let labels := ungroup groups
  if (group labels).entries = groups.entries then some labels else none

/-- Representative-map layout. This codec preserves the supplied labels. -/
def representativeMap (key : TotalCodec Key (Tree Ref Name)) :
    TotalCodec (OrderedMap Key Key) (Tree Ref Name) := pairMap key key

def encodeCanonical (codec : TotalCodec (OrderedMap Key Key) Target) (labels : OrderedMap Key Key) : Target :=
  codec.encode (PER.Partition.normalize labels)

def encodeCanonical? (codec : PartialCodec (OrderedMap Key Key) Target) (labels : OrderedMap Key Key) : Option Target :=
  codec.encode? (PER.Partition.normalize labels)

def decodePartition? (codec : PartialCodec (OrderedMap Key Key) Target) (repr : Target) : Option (PER Key) :=
  (codec.decode? repr).map fun labels => PER.fibers labels.lookup?

abbrev decodePartition (codec : TotalCodec (OrderedMap Key Key) Target) (repr : Target) : Option (PER Key) :=
  decodePartition? codec.partial repr

end Silmaril.Formats.Dasl.Encode.Partition
