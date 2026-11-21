module

public import Silmaril.Formats.Dasl.Encode.Collection.Defs

public section

namespace Silmaril.Formats.Dasl.Encode

open Silmaril.Semantics

variable {Target Key Item : Type}

theorem representsMap_iff_finite [LinearOrder Key] (codec : TotalCodec (OrderedMap Key Item) Target)
    (lookup : Key → Option Item) :
    (∃ repr, RepresentsMap codec repr lookup) ↔ (OrderedMap.support lookup).Finite := by
  rw [OrderedMap.finite_support_iff]
  exact ⟨fun ⟨_, map, _, h⟩ => ⟨map, h⟩, fun ⟨map, h⟩ => ⟨codec.encode map, map, codec.recovers map, h⟩⟩

theorem representsSet_iff_finite [DecidableEq Key] (codec : TotalCodec (Finset Key) Target) (members : Set Key) :
    (∃ repr, RepresentsSet codec repr members) ↔ members.Finite := by
  constructor
  · rintro ⟨_, keys, _, rfl⟩; exact keys.finite_toSet
  · intro h; exact ⟨_, h.toFinset, codec.recovers _, h.coe_toFinset⟩

theorem encode_map_eq_iff [LinearOrder Key] (codec : TotalCodec (OrderedMap Key Item) Target)
    (left right : OrderedMap Key Item) : codec.encode left = codec.encode right ↔ left.lookup? = right.lookup? :=
  ⟨fun h => congrArg OrderedMap.lookup? (codec.injective h),
   fun h => congrArg codec.encode (OrderedMap.eq_of_lookup (congrFun h))⟩

theorem encode_set_eq_iff [DecidableEq Key] (codec : TotalCodec (Finset Key) Target)
    (left right : Finset Key) : codec.encode left = codec.encode right ↔ (left : Set Key) = (right : Set Key) :=
  ⟨fun h => congrArg (fun keys : Finset Key => (keys : Set Key)) (codec.injective h),
   fun h => congrArg codec.encode (Finset.coe_injective h)⟩

end Silmaril.Formats.Dasl.Encode
