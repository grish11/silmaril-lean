module

public import Mathlib.Order.Sum.Order
public import Silmaril.Formats.Dasl.Prolly.Operations.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Prolly.LinkKey

open Silmaril.Semantics

variable {Name : Type}

/-- Compare by the supplied name order within a lane, with objects before
blobs. Different names remain different keys even if they resolve to equal
targets. The same name in the two lanes is also a pair of distinct keys. -/
abbrev Mixed (Name : Type) := Name ⊕ₗ Name

def tagged : Link Name → Mixed Name
  | .obj name => toLex (.inl name)
  | .blob name => toLex (.inr name)

def untag : Mixed Name → Link Name := fun key =>
  match ofLex key with
  | .inl name => .obj name
  | .inr name => .blob name

abbrev object : Encode.TotalCodec Name (Shallow Name) := objectLink

def blob : Encode.TotalCodec Name (Shallow Name) :=
  ⟨fun name => .ref (.blob name), (fun | .ref (.blob name) => some name | _ => none), fun _ => rfl⟩

def mixed : Encode.TotalCodec (Mixed Name) (Shallow Name) :=
  (show Encode.TotalCodec (Mixed Name) (Link Name) from
    ⟨untag, some ∘ tagged, fun key => by cases key <;> rfl⟩).then Encode.link

abbrev Map (Name Payload : Type) [LinearOrder Name] := OrderedMap (Mixed Name) Payload
abbrev Set (Name : Type) [LinearOrder Name] := OrderedSet (Mixed Name)

/-- Select the key and payload codecs, without changing the block grammar,
structural object-link lane, or any of the finite operations. -/
def profile {Key Payload : Type} (keys : Encode.TotalCodec Key (Shallow Name))
    (payload : Encode.TotalCodec Payload (Shallow Name)) (policy : Semantics.Prolly.Policy Key)
    (render? : Shallow Name → Option ByteArray) (name? : ByteArray → Option Name) : RootProfile Name Key Payload :=
  ⟨policy, keys, payload, render?, name?⟩

end Silmaril.Formats.Dasl.Prolly.LinkKey
