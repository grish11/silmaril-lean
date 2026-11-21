module

public import Silmaril.Formats.Dasl.Wire.Defs
public import Silmaril.Semantics.Naming.Thms
import Silmaril.Proofs.Formats.Dasl.Wire

public section

namespace Silmaril.Formats.Dasl.Wire

open Silmaril.Formats Silmaril.Formats.Cbor Silmaril.Semantics.Naming

/-- The ordered syntax adapter preserves indexed lists, finite maps, typed links, and scalars. -/
theorem lower_toOrdered {Name : Type} (value : Shallow Name) : lower (toOrdered value) = value :=
  Proofs.Formats.Dasl.Wire.lower_toOrdered value

theorem typed_cid_parse_iff {bytes : List UInt8} {link : Link Cid} :
    cidCodec.parse? bytes = some link ↔ cidCodec.bytes link = bytes ∧ ValidLink link :=
  ⟨Proofs.Formats.Dasl.Wire.typed_cid_parse,
   fun ⟨same, valid⟩ => same ▸ Proofs.Formats.Dasl.Wire.typed_cid_roundtrip valid⟩

theorem lower_map_perm {Name : Type} {left right : List (String × Drisl.OrderedATProto (Link Name))}
    (distinct : (left.map Prod.fst).Nodup) (order : left.Perm right) :
    lower (.map (.ofEntries left)) = lower (.map (.ofEntries right)) :=
  Proofs.Formats.Dasl.Wire.lower_map_perm distinct order

theorem dictFields_materialize_perm {Name : Type} (fields : List (String × Shallow Name))
    (distinct : (fields.map Prod.fst).Nodup) :
    ((dictFields fields).1.sort.attach.map (fun key =>
      (key.val, (dictFields fields).2 ⟨key.val, (Finset.mem_sort _).mp key.property⟩))).Perm fields :=
  Proofs.Formats.Dasl.Wire.dictFields_materialize_perm fields distinct

/-- Canonical bytes, recursive wire key order and typed interpretation are checked before
discarding the order; this does not yet prove that the abstract serializer is an inverse. -/
theorem parse_eq_some_iff {bytes : ByteArray} {tree : Shallow Cid} :
    parse? bytes = some tree ↔
      ∃ value ordered, Cbor.decode bytes.data.toList = some value ∧ value.encode = bytes.data.toList ∧
        Drisl.canonicalMaps value = true ∧ Drisl.interpretCbor? Drisl.i64Cbor cidCodec value = some ordered ∧
        lower ordered = tree :=
  Proofs.Formats.Dasl.Wire.parse_eq_some_iff

theorem i64_roundtrip (bits : UInt64) :
    (Drisl.i64Cbor.readNumber? (Drisl.i64Cbor.number bits.toInt64)).map Int64.toUInt64 = some bits :=
  Proofs.Formats.Dasl.i64_roundtrip bits

theorem object_raw_disjoint {name : Cid} (object : IsObjectCid name) (raw : IsRawCid name) : False :=
  (by decide : (0x71 : UInt8) ≠ 0x55) (Option.some.inj (object.symm.trans raw))

theorem codec_disjoint_domains {store : Stores Cid (Shallow Cid) ByteArray}
    (objects : ∀ ⦃name payload⦄, store.objects name payload → IsObjectCid name)
    (blobs : ∀ ⦃name payload⦄, store.blobs name payload → IsRawCid name) : store.DisjointDomains := by
  intro name obj blob object raw
  exact object_raw_disjoint (objects object) (blobs raw)

theorem serializes_binding : Binding Serializes := by
  intro value left right first second
  exact Option.some.inj (first.1.symm.trans second.1)

theorem flatten_binding {store : Stores Cid (Shallow Cid) ByteArray} (bound : store.Binding)
    (domains : store.DisjointDomains) : Binding (store.flatten Serializes) :=
  bound.flatten domains serializes_binding

theorem push_parse_iff {objects : Relation Cid (Shallow Cid)} {name wire value}
    (parsed : parse? wire = some value) :
    push objects Serializes name wire ↔ objects name value ∧ Serializes value wire :=
  Silmaril.Semantics.Naming.push_parse_iff (by intro source bytes encoded; exact encoded.2) parsed

end Silmaril.Formats.Dasl.Wire
