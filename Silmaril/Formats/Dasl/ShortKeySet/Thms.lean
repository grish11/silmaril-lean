module

public import Silmaril.Formats.Dasl.ShortKeySet.Defs
import Silmaril.Proofs.Formats.Dasl.ShortKeySet

public section

namespace Silmaril.Formats.Dasl.ShortKeySet

open Silmaril.Semantics (OrderedSet OrderedMap)

variable {Name : Type} {limit : Fin 256}

theorem pack_length (keys : List (Bytes limit)) :
    (pack keys).length = (keys.map fun key => key.val.length + 1).sum := by
  induction keys with
  | nil => rfl
  | cons key tail ih => simp [pack, ih, Nat.add_assoc, Nat.add_comm]

theorem pack_key_count_le (keys : List (Bytes limit)) : keys.length ≤ (pack keys).length := by
  induction keys with
  | nil => rfl
  | cons key tail ih => simp [pack]; omega

def packing : Encode.TotalCodec (List (Bytes limit)) Prolly.ByteKey :=
  ⟨pack, (fun bytes => unpack limit bytes.length bytes),
    fun keys => Proofs.Formats.Dasl.ShortKeySet.unpack_pack keys (pack_key_count_le keys)⟩

theorem pack_of_unpacked {raw : Prolly.ByteKey} {keys : List (Bytes limit)} {fuel : Nat}
    (hit : unpack limit fuel raw = some keys) : pack keys = raw :=
  Proofs.Formats.Dasl.ShortKeySet.pack_of_unpacked hit

def utf8 : Encode.TotalCodec (Text limit) (Bytes limit) :=
  ⟨Text.octets, Text.fromOctets?, Proofs.Formats.Dasl.ShortKeySet.octets_recovers⟩

/-- Alternative flat layout: one inline byte string instead of an array. -/
def packedBytesCodec : Encode.TotalCodec (OrderedSet (Bytes limit)) (Shallow Name) :=
  Encode.setKeys.then (packing.then Prolly.byteKey)

/-- The same byte framing, but each key must decode as exact UTF-8 text.
The final order check uses recovered `String` values. -/
def packedTextCodec : Encode.TotalCodec (OrderedSet (Text limit)) (Shallow Name) :=
  Encode.setKeys.then (utf8.listCodec.then (packing.then Prolly.byteKey))

section Semantics

variable {Key : Type} [LinearOrder Key]

@[simp] theorem members_ofFinset (keys : Finset Key) : members (ofFinset keys) = keys := by
  simp [members, ofFinset, OrderedMap.keys, List.map_map, Function.comp_def]

@[simp] theorem ofFinset_members (layout : OrderedSet Key) : ofFinset (members layout) = layout :=
  Proofs.Formats.Dasl.ShortKeySet.ofFinset_members layout

def equiv : OrderedSet Key ≃ Finset Key := ⟨members, ofFinset, ofFinset_members, members_ofFinset⟩

theorem normalize_eq_iff (left right : List Key) :
    normalize left = normalize right ↔ ∀ key, key ∈ left ↔ key ∈ right := by
  rw [← equiv.injective.eq_iff]; change members (ofFinset left.toFinset) = members (ofFinset right.toFinset) ↔ _
  simp [Finset.ext_iff]

theorem contains_iff (layout : OrderedSet Key) (key : Key) : contains layout key = true ↔ key ∈ members layout := by
  simp [contains, members]

theorem cardinality_eq (layout : OrderedSet Key) : cardinality layout = (members layout).card :=
  (List.toFinset_card_of_nodup layout.keys_nodup).symm

end Semantics

end Silmaril.Formats.Dasl.ShortKeySet
