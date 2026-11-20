module

public import Silmaril.Formats.Dasl.Prolly.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Prolly

open Silmaril.Semantics Silmaril.Semantics.Prolly

variable {Name Key Payload : Type}

/-- A profile fixes all choices used by the builder and by bottom-up naming.
The key order is supplied separately. Both serialization and the abstract naming
function may fail. No implementation of a hash algorithm is required. -/
structure RootProfile (Name Key Payload : Type) where
  policy : Policy Key
  key : Encode.TotalCodec Key (Shallow Name)
  payload : Encode.TotalCodec Payload (Shallow Name)
  render? : Shallow Name → Option ByteArray
  hash? : ByteArray → Option Name

namespace RootProfile

def ofTotalHash (policy : Policy Key) (key : Encode.TotalCodec Key (Shallow Name))
    (payload : Encode.TotalCodec Payload (Shallow Name)) (render? : Shallow Name → Option ByteArray)
    (hash : ByteArray → Name) : RootProfile Name Key Payload :=
  ⟨policy, key, payload, render?, some ∘ hash⟩

def nameBlock? (profile : RootProfile Name Key Payload) (block : Block Name Key Payload) : Option Name :=
  ((encodeBlock profile.key profile.payload block).bind profile.render?).bind profile.hash?

def rootName? [LinearOrder Key] (profile : RootProfile Name Key Payload) (map : OrderedMap Key Payload) : Option Name :=
  (build profile.policy map).rootName? profile.nameBlock?

/-- Any ordered representation of the semantic lookup map may contribute a root,
but it must use the fixed builder, codecs and naming profile at every block. -/
def Roots [LinearOrder Key] (profile : RootProfile Name Key Payload) :
    Naming.Relation Name (Key → Option Payload) :=
  fun name lookup => ∃ (map : OrderedMap Key Payload) (address : Block Name Key Payload → Name),
    (∀ key, map.lookup? key = lookup key) ∧
    (build profile.policy map).Admits profile.nameBlock? address ∧ (build profile.policy map).rootName address = name

/-- Exactly the shallow object observations of this addressed tree. No raw/blob
bindings are contributed here. An unencodable block contributes no observation;
use `Tree.Admits` to ensure no such block occurs. -/
def observations (profile : RootProfile Name Key Payload) (tree : Semantics.Prolly.Tree Key Payload)
    (address : Block Name Key Payload → Name) : Store Name :=
  ⟨Naming.push (tree.observations address) (fun block value => encodeBlock profile.key profile.payload block = some value),
    fun _ _ => False⟩

/-- Push shallow observations through the renderer. This alone says nothing
about parsing, collision freedom, or raw store admission. -/
def byteObservations (profile : RootProfile Name Key Payload) (tree : Semantics.Prolly.Tree Key Payload)
    (address : Block Name Key Payload → Name) : Naming.Relation Name ByteArray :=
  Naming.push (profile.observations tree address).objects (Naming.graph profile.render?)

end RootProfile
end Silmaril.Formats.Dasl.Prolly
