module

public import Silmaril.Formats.Dasl.Prolly.Root.Publish.Defs
public import Silmaril.Formats.Dasl.Prolly.Scan.Defs
public import Silmaril.Semantics.Prolly.Operations.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Prolly

open Silmaril.Semantics Silmaril.Semantics.Prolly

variable {Name Key Payload Error : Type}

/-- Every reached structural block is readable and agrees exactly with the AST.
This makes no claim about targets referenced by a key or payload codec. -/
def WholeReads (read : Name → Except (Fault Name) (Block Name Key Payload))
    (address : Block Name Key Payload → Name) (tree : Semantics.Prolly.Tree Key Payload) : Prop :=
  ∀ block ∈ blockOccurrences address tree.level tree.root, read (address block) = .ok block

def acquire [LinearOrder Key] (codec : Encode.PartialCodec (Block Name Key Payload) (Shallow Name))
    (read : Read Name) (width fuel : Nat) (root : Name) : Except (Fault Name) (OrderedMap Key Payload) := do
  let entries ← scan (readBlock codec read) width fuel none root
  match OrderedMap.ofEntries? entries with
  | some map => .ok map
  | none => .error (.invalidNode root)

namespace RootProfile

def Readback.shallowRead {profile : RootProfile Name Key Payload} (reader : profile.Readback)
    (read : Name → Option ByteArray) : Read Name := fun name =>
  match read name with
  | none => .missing
  | some bytes => match reader.decode? bytes with
    | none => .invalidWire
    | some value => .found value

/-- Only the decoded object view of this snapshot; not a claim about blobs,
integrity or the resolution of any embedded link. -/
def Readback.objectView {profile : RootProfile Name Key Payload} (reader : profile.Readback)
    (read : Name → Option ByteArray) : Store Name :=
  ⟨fun name value => reader.shallowRead read name = .found value, fun _ _ => False⟩

inductive CombineFailure (Name Error : Type) where
  | left (fault : Fault Name)
  | right (fault : Fault Name)
  | overlap (error : Error)
  | publish (error : PublishFailure Name)
  deriving DecidableEq, Repr

/-- Closed rebuild against an authoritative snapshot. Structural blocks alone
are acquired. Overlap errors and acquisition faults occur before publication. -/
def combineAndPublish [DecidableEq Name] [LinearOrder Key] (profile : RootProfile Name Key Payload)
    (reader : profile.Readback) (kind : OrderedMap.Combine) (overlap : OrderedMap.Overlap Key Payload Error)
    (read : Name → Option ByteArray) (fuel : Nat) (leftRoot rightRoot : Name) :
    Except (CombineFailure Name Error) (Name × (Name → Option ByteArray)) := do
  let codec := blockCodec profile.key profile.payload
  let left ← (acquire codec (reader.shallowRead read) profile.policy.width fuel leftRoot).mapError .left
  let right ← (acquire codec (reader.shallowRead read) profile.policy.width fuel rightRoot).mapError .right
  let result ← (left.combine kind overlap right).mapError .overlap
  (profile.publishMap reader result read).mapError .publish

/-- Valid canonical roots in the given store, not just available outputs of a
naming function. The selected profile must name every reached block. -/
def ValidRoots [LinearOrder Key] (profile : RootProfile Name Key Payload) (store : Store Name) :
    Naming.Relation Name (Key → Option Payload) := fun name lookup =>
  ∃ (map : OrderedMap Key Payload) (address : Block Name Key Payload → Name),
    (∀ key, map.lookup? key = lookup key) ∧
    (build profile.policy map).Admits profile.nameBlock? address ∧
    (build profile.policy map).rootName address = name ∧
    Stored (blockCodec profile.key profile.payload) address (build profile.policy map) store

end RootProfile
end Silmaril.Formats.Dasl.Prolly
