module

public import Silmaril.Formats.Dasl.Mst.Build.Thms
public import Silmaril.Semantics.Naming.Admission.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Mst

open Silmaril.Semantics.Naming

variable {Name : Type}

structure PublishProfile (Name : Type) where
  wire : Encode.PartialCodec (Shallow Name) ByteArray
  name? : ByteArray → Option Name

def PublishProfile.nodeBytes (profile : PublishProfile Name) : Encode.PartialCodec (Node Name) ByteArray :=
  nodeCodec.then profile.wire

def PublishProfile.nameNode? (profile : PublishProfile Name) (node : Node Name) : Option Name :=
  (profile.nodeBytes.encode? node).bind profile.name?

def PublishProfile.byteObservations (profile : PublishProfile Name) (built : Built Name) : Relation Name ByteArray :=
  push built.observed (graph profile.nodeBytes.encode?)

def PublishProfile.reference (profile : PublishProfile Name) (read : Name → Option ByteArray) : Relation Name (Node Name) :=
  push (graph read) (graph profile.nodeBytes.decode?)

def PublishProfile.readShallow (profile : PublishProfile Name) (read : Name → Option ByteArray)
    (name : Name) : Wire.ReadResult (Shallow Name) :=
  match read name with
  | none => .missing
  | some bytes => match profile.wire.decode? bytes with
    | none => .invalidWire
    | some value => .found value

def PublishProfile.renderBlock? (profile : PublishProfile Name) (block : Name × Node Name) : Option (Name × ByteArray) :=
  (profile.nodeBytes.encode? block.2).map fun bytes => (block.1, bytes)

inductive PublishError (Name : Type) where
  | construction
  | collision (name : Name)
  deriving DecidableEq, Repr

/-- Reuse the names chosen by construction. Admit raw bytes without filtering
malformed present data, and return no staged snapshot on conflict. -/
def PublishProfile.publish [DecidableEq Name] (profile : PublishProfile Name) (layerOf : Key → Nat)
    (records : List (Record Name)) (read : Name → Option ByteArray) :
    Except (PublishError Name) (Name × (Name → Option ByteArray)) := do
  let some built := build layerOf profile.nameNode? records | .error .construction
  let some writes := built.blocks.mapM profile.renderBlock? | .error .construction
  match admit read writes with
  | .error name => .error (.collision name)
  | .ok staged => .ok (built.root, staged)

def Atproto.publish [DecidableEq Name] (profile : PublishProfile Name) (records : List (Record Name))
    (read : Name → Option ByteArray) : Except (PublishError Name) (Name × (Name → Option ByteArray)) :=
  profile.publish keyLayer records read

/-- In addition to the exact byte update, all newly named blocks can be read back
and the decoded snapshot satisfies the same rooted invariant as construction. -/
def PublishProfile.Spec (profile : PublishProfile Name) (layerOf : Key → Nat) (records : List (Record Name))
    (read : Name → Option ByteArray) (built : Built Name)
    (result : Except (PublishError Name) (Name × (Name → Option ByteArray))) : Prop :=
  let requested := union (graph read) (profile.byteObservations built)
  match result with
  | .ok (root, staged) => root = built.root ∧ graph staged = requested ∧
      Subset built.observed (profile.reference staged) ∧ Realizes layerOf (profile.reference staged) none root records
  | .error (.collision name) => name ∈ collisions requested
  | .error .construction => False

end Silmaril.Formats.Dasl.Mst
