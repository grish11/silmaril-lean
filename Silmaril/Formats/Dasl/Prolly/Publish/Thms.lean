module

public import Silmaril.Formats.Dasl.Prolly.Publish.Defs
public import Silmaril.Semantics.Naming.Admission.Thms
import Silmaril.Proofs.Formats.Dasl.ProllyPublish

public section

namespace Silmaril.Formats.Dasl.Prolly

open Silmaril.Semantics.Naming
open Silmaril.Semantics.Prolly (Block)

variable {Name Key Payload : Type} [DecidableEq Name]

/-- Successful publication preserves all existing raw bindings, stores the named
tree, and preserves hash policy if the original snapshot respected it. The
returned snapshot is binding by `graph_binding`, not by hash injectivity. -/
theorem publish_sound {codec : Encode.PartialCodec (Block Name Key Payload) (Shallow Name)}
    {wire : Encode.PartialCodec (Shallow Name) ByteArray} {address : Block Name Key Payload → Name}
    {hash : ByteArray → Name} {tree : Semantics.Prolly.Tree Key Payload} {read staged : Name → Option ByteArray}
    {root : Name} (blobs : Relation Name ByteArray)
    (accepted : publish codec wire address hash tree read = .ok (root, staged)) :
    root = tree.rootName address ∧ Subset (graph read) (graph staged) ∧
      Stored codec address tree (objectByteView wire staged blobs) ∧
      (HashCompatible hash (graph read) → HashCompatible hash (graph staged)) :=
  Proofs.Formats.Dasl.ProllyPublish.publish_sound blobs accepted

end Silmaril.Formats.Dasl.Prolly
