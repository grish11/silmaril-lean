module

public import Silmaril.Semantics.OrderedMap.Operations.Thms
public import Silmaril.Semantics.OrderedMap.Transport.Defs
import Silmaril.Proofs.Semantics.OrderedMap.Transport

public section

namespace Silmaril.Semantics.OrderedMap

variable {Key Next Payload Error : Type} [LinearOrder Key] [LinearOrder Next]

@[simp] theorem lookup_rekey (map : OrderedMap Key Payload) (key : Key ↪o Next) (source : Key) :
    (map.rekey key).lookup? (key source) = map.lookup? source :=
  Proofs.Semantics.OrderedMap.Transport.lookup_rekey map key source

theorem lookup_rekey_outside (map : OrderedMap Key Payload) (key : Key ↪o Next) (target : Next)
    (outside : target ∉ Set.range key) : (map.rekey key).lookup? target = none :=
  Proofs.Semantics.OrderedMap.Transport.lookup_rekey_outside map key target outside

@[simp] theorem cardinality_rekey (map : OrderedMap Key Payload) (key : Key ↪o Next) :
    (map.rekey key).cardinality = map.cardinality := by simp [rekey, cardinality]

/-- Successful union/intersection is invariant under an injective order-preserving
key transport with coherent overlap decisions. This is not a root-name theorem. -/
theorem rekey_combine_iff (key : Key ↪o Next) (kind : Combine)
    (overlap : Overlap Key Payload Error) (nextOverlap : Overlap Next Payload Error)
    (agrees : ∀ source left right, nextOverlap (key source) left right = overlap source left right)
    (left right result : OrderedMap Key Payload) :
    (left.rekey key).combine kind nextOverlap (right.rekey key) = .ok (result.rekey key) ↔
      left.combine kind overlap right = .ok result :=
  Proofs.Semantics.OrderedMap.Transport.rekey_combine_iff key kind overlap nextOverlap agrees left right result

end Silmaril.Semantics.OrderedMap
