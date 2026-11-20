module

public import Silmaril.Formats.Dasl.Prolly.Root.Defs
public import Silmaril.Formats.Dasl.Prolly.Publish.Defs
public import Silmaril.Formats.Dasl.Prolly.Thms

@[expose] public section

namespace Silmaril.Formats.Dasl.Prolly.RootProfile

open Silmaril.Semantics Silmaril.Semantics.Prolly

variable {Name Key Payload : Type}

/-- The reader recovers the shallow values that this profile emits. It may
accept other bytes; publication uses the renderer, not those other spellings. -/
structure Readback (profile : RootProfile Name Key Payload) where
  decode? : ByteArray → Option (Shallow Name)
  recovers : ∀ ⦃value bytes⦄, profile.render? value = some bytes → decode? bytes = some value

def Readback.codec {profile : RootProfile Name Key Payload} (reader : profile.Readback) :
    Encode.PartialCodec (Shallow Name) ByteArray :=
  ⟨profile.render?, reader.decode?, reader.recovers⟩

def Readback.readBlock? {profile : RootProfile Name Key Payload} (reader : profile.Readback)
    (read : Name → Option ByteArray) (name : Name) : Option (Block Name Key Payload) :=
  ((read name).bind reader.decode?).bind (blockCodec profile.key profile.payload).decode?

inductive PublishFailure (Name : Type) where
  | naming
  | publishing (reason : PublishError Name)
  deriving DecidableEq, Repr

/-- Name first; only then pass the addressed tree to the raw atomic transaction.
The total replay functions cannot fill a failed naming decision on a reached block. -/
def publishTree [DecidableEq Name] (profile : RootProfile Name Key Payload) (reader : profile.Readback)
    (tree : Semantics.Prolly.Tree Key Payload) (read : Name → Option ByteArray) :
    Except (PublishFailure Name) (Name × (Name → Option ByteArray)) :=
  match tree.rootName? profile.nameBlock? with
  | none => .error .naming
  | some root =>
    (Prolly.publish (blockCodec profile.key profile.payload) reader.codec (replayAddress profile.nameBlock? root)
      (fun bytes => (profile.hash? bytes).getD root) tree read).mapError .publishing

/-- This operation builds the entire new map, not an incremental rebucketing. -/
def publishMap [DecidableEq Name] [LinearOrder Key] (profile : RootProfile Name Key Payload)
    (reader : profile.Readback) (map : OrderedMap Key Payload) (read : Name → Option ByteArray) :
    Except (PublishFailure Name) (Name × (Name → Option ByteArray)) :=
  profile.publishTree reader (build profile.policy map) read

/-- Soundness and exact admission after successful naming. A collision is about
authoritative bytes, even when the prior bytes do not decode. -/
def PublicationSpec (profile : RootProfile Name Key Payload) (reader : profile.Readback)
    (tree : Semantics.Prolly.Tree Key Payload) (read : Name → Option ByteArray) (root : Name)
    (result : Except (PublishFailure Name) (Name × (Name → Option ByteArray))) : Prop :=
  let address := replayAddress profile.nameBlock? root
  let requested := Naming.union (Naming.graph read) (profile.byteObservations tree address)
  match result with
  | .ok (published, staged) => published = root ∧ Naming.graph staged = requested ∧
      ∀ block ∈ blockOccurrences address tree.level tree.root, reader.readBlock? staged (address block) = some block
  | .error (.publishing (.collision name)) => name ∈ Naming.collisions requested
  | .error _ => False

end Silmaril.Formats.Dasl.Prolly.RootProfile
