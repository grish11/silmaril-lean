module

public import Silmaril.Formats.Dasl.Prolly.Defs
public import Silmaril.Semantics.Naming.Admission.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Prolly

open Silmaril.Semantics.Prolly (Block blockOccurrences)
open Silmaril.Semantics.Naming (admit graph Relation)

variable {Name Key Payload : Type}

inductive PublishError (Name : Type) where
  | blockEncoding (name : Name)
  | wireEncoding (name : Name)
  | invalidAddress (name : Name)
  | collision (name : Name)
  deriving DecidableEq, Repr

def prepareBlock [DecidableEq Name] (codec : Encode.PartialCodec (Block Name Key Payload) (Shallow Name))
    (wire : Encode.PartialCodec (Shallow Name) ByteArray) (address : Block Name Key Payload → Name)
    (hash : ByteArray → Name) (block : Block Name Key Payload) : Except (PublishError Name) (Name × ByteArray) := do
  let name := address block
  let some value := codec.encode? block | .error (.blockEncoding name)
  let some bytes := wire.encode? value | .error (.wireEncoding name)
  if hash bytes = name then .ok (name, bytes) else .error (.invalidAddress name)

/-- Publish a fully rebuilt tree by staging every serialized block, then checking
the whole batch against authoritative *raw* object bytes. An equal existing
block is reused; any different byte string is a collision, even if malformed.
This is a pure transaction result, not a concurrent storage protocol. -/
def publish [DecidableEq Name] (codec : Encode.PartialCodec (Block Name Key Payload) (Shallow Name))
    (wire : Encode.PartialCodec (Shallow Name) ByteArray) (address : Block Name Key Payload → Name)
    (hash : ByteArray → Name) (tree : Semantics.Prolly.Tree Key Payload) (read : Name → Option ByteArray) :
    Except (PublishError Name) (Name × (Name → Option ByteArray)) := do
  let writes ← (blockOccurrences address tree.level tree.root).mapM (prepareBlock codec wire address hash)
  match admit read writes with
  | .ok staged => .ok (tree.rootName address, staged)
  | .error name => .error (.collision name)

/-- Interpret the dedicated object-byte partition. The independent blob relation
is carried through unchanged. This view is not the snapshot used for admission. -/
def objectByteView (wire : Encode.PartialCodec (Shallow Name) ByteArray) (read : Name → Option ByteArray)
    (blobs : Relation Name ByteArray) : Store Name :=
  ⟨graph (fun name => (read name).bind wire.decode?), blobs⟩

end Silmaril.Formats.Dasl.Prolly
