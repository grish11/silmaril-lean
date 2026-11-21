module

public import Mathlib.Order.Hom.Basic
public import Silmaril.Semantics.OrderedMap.Operations.Defs

@[expose] public section

namespace Silmaril.Semantics.OrderedMap

variable {Key Next Payload : Type} [LinearOrder Key] [LinearOrder Next]

/-- Rename keys without sorting, aliasing or choosing a winning payload. This
does not transport a bucket policy, serialization, or a CAS name. -/
def rekey (map : OrderedMap Key Payload) (key : Key ↪o Next) : OrderedMap Next Payload :=
  ⟨map.entries.map (fun entry => (key entry.1, entry.2)),
    List.pairwise_map.mpr (map.ordered.imp fun ordered => key.strictMono ordered)⟩

end Silmaril.Semantics.OrderedMap
