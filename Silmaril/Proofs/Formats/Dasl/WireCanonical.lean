module

public import Silmaril.Formats.Dasl.Wire.Canonical.Defs
public import Silmaril.Formats.Dasl.Wire.Thms
public import Silmaril.Formats.Cbor.Drisl.Model.Thms
public import Silmaril.Formats.Cbor.Value.Thms
import Silmaril.Proofs.Formats.Dasl.WireCanonicalReprint

public section

namespace Silmaril.Proofs.Formats.Dasl.WireCanonical

open Silmaril.Formats Silmaril.Formats.Cbor Silmaril.Formats.Dasl Silmaril.Formats.Dasl.Wire

variable {Name : Type}

private theorem emit_fields (cid : Drisl.CidCodec (Link Name))
    (fields : RawSyn String (Drisl.Scalar Int64 (Link Name)) .obj) :
    Drisl.emitModel Drisl.i64Cbor cid false fields =
      fields.toEntries.map (fun pair => (Drisl.utf8Value pair.1, Drisl.emitModel Drisl.i64Cbor cid false pair.2)) := by
  have aux (entries : List (String × Drisl.OrderedATProto (Link Name))) :
      Drisl.emitModel Drisl.i64Cbor cid false (RawSyn.ofEntries entries) =
        entries.map (fun pair => (Drisl.utf8Value pair.1, Drisl.emitModel Drisl.i64Cbor cid false pair.2)) := by
    induction entries with
    | nil => rfl
    | cons field tail ih => simp [Drisl.emitModel, ih]
  simpa using aux fields.toEntries

theorem emit_canonical (cid : Drisl.CidCodec (Link Name)) {index : JsonIx}
    (input : RawSyn String (Drisl.Scalar Int64 (Link Name)) index) :
    Drisl.emitModel Drisl.i64Cbor cid false (canonicalOrder input) = Drisl.emitModel Drisl.i64Cbor cid true input := by
  induction input with
  | scalar | nil | objNil => rfl
  | list items ih => simp [canonicalOrder, Drisl.emitModel, ih]
  | cons first tail ihFirst ihTail | objCons key first tail ihFirst ihTail =>
    simp [canonicalOrder, Drisl.emitModel, ihFirst, ihTail]
  | map fields ih =>
    rw [canonicalOrder, Drisl.emitModel, Drisl.emitModel]
    simp only [Bool.false_eq_true, ite_false, ite_true]
    congr 1
    rw [emit_fields, RawSyn.toEntries_ofEntries,
      List.map_mergeSort (r := fun left right => keyLE left.1 right.1)
        (f := fun pair : String × Drisl.OrderedATProto (Link Name) =>
        (Drisl.utf8Value pair.1, Drisl.emitModel Drisl.i64Cbor cid false pair.2))
        (s := fun left right => !Drisl.lexLt right.1.encode left.1.encode) (fun _ _ _ _ => rfl), ← emit_fields, ih]

private theorem canonical_keys : (fields : RawSyn String (Drisl.Scalar Int64 (Link Name)) .obj) →
    (canonicalOrder fields).keys = fields.keys
  | .objNil => rfl
  | .objCons _ _ tail => by simp [canonicalOrder, canonical_keys tail]

private theorem lower_order {index : JsonIx} (input : RawSyn String (Drisl.Scalar Int64 (Link Name)) index)
    (unique : JsonWithBytes.uniqueKeys input = true) : lower (canonicalOrder input) = lower input := by
  induction input with
  | scalar | nil | objNil => rfl
  | list items ih =>
    rw [canonicalOrder, lower, lower, ih unique]
  | cons head tail ihHead ihTail | objCons key head tail ihHead ihTail =>
    rw [JsonWithBytes.uniqueKeys, Bool.and_eq_true] at unique
    simp [canonicalOrder, lower, ihHead unique.1, ihTail unique.2]
  | map fields ih =>
    rw [JsonWithBytes.uniqueKeys, Bool.and_eq_true, decide_eq_true_eq] at unique
    have distinct : ((canonicalOrder fields).toEntries.map Prod.fst).Nodup := by
      rw [← RawSyn.keys_eq_toEntries_fst, canonical_keys]
      exact unique.1
    rw [canonicalOrder, ← lower_map_perm (left := (canonicalOrder fields).toEntries) distinct (List.mergeSort_perm _ _).symm,
      RawSyn.ofEntries_toEntries, lower, lower, ih unique.2]

private theorem scalars_fields (fields : List (String × Drisl.OrderedATProto (Link Name))) :
    (RawSyn.ofEntries fields).scalars = fields.flatMap (fun field => field.2.scalars) := by
  induction fields with
  | nil => rfl
  | cons head tail ih => simp [RawSyn.scalars, ih]

private theorem scalars_order {index : JsonIx} (input : RawSyn String (Drisl.Scalar Int64 (Link Name)) index) :
    List.Perm (canonicalOrder input).scalars input.scalars := by
  induction input with
  | scalar | nil | objNil => exact .rfl
  | list items ih => exact ih
  | cons head tail ihHead ihTail | objCons key head tail ihHead ihTail => exact ihHead.append ihTail
  | map fields ih =>
    change List.Perm (RawSyn.ofEntries ((canonicalOrder fields).toEntries.mergeSort _)).scalars fields.scalars
    rw [scalars_fields]
    apply (List.Perm.flatMap_right (fun field : String × Drisl.OrderedATProto (Link Name) => field.2.scalars)
      (List.mergeSort_perm (canonicalOrder fields).toEntries (fun left right => keyLE left.1 right.1))).trans
    rwa [← scalars_fields, RawSyn.ofEntries_toEntries]

theorem links_order {index : JsonIx} (input : RawSyn String (Drisl.Scalar Int64 (Link Name)) index) :
    List.Perm (Drisl.links (canonicalOrder input)) (Drisl.links input) :=
  (scalars_order input).filterMap _

private theorem unique_list (items : List (Drisl.OrderedATProto (Link Name)))
    (unique : ∀ item ∈ items, JsonWithBytes.uniqueKeys item = true) :
    JsonWithBytes.uniqueKeys (RawSyn.ofList items) = true := by
  induction items with
  | nil => rfl
  | cons item tail ih =>
    exact Bool.and_eq_true_iff.mpr ⟨unique _ (.head _), ih (fun next mem => unique next (.tail _ mem))⟩

private theorem unique_fields (fields : List (String × Drisl.OrderedATProto (Link Name)))
    (unique : ∀ field ∈ fields, JsonWithBytes.uniqueKeys field.2 = true) :
    JsonWithBytes.uniqueKeys (RawSyn.ofEntries fields) = true := by
  induction fields with
  | nil => rfl
  | cons field tail ih =>
    exact Bool.and_eq_true_iff.mpr ⟨unique _ (.head _), ih (fun next mem => unique next (.tail _ mem))⟩

theorem projection (value : Shallow Name) : lower (canonicalOrder (toOrdered value)) = value := by
  refine (lower_order (toOrdered value) ?_).trans (lower_toOrdered value)
  induction value with
  | obj impossible _ _ | blob impossible _ => exact impossible.elim
  | ref | i64 | bytes | string | bool | null => rfl
  | list len values ih =>
    apply unique_list
    intro item member
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
    exact ih index
  | dict keys values ih =>
    let fields : List (String × Drisl.OrderedATProto (Link Name)) := keys.sort.attach.map fun key =>
      (key.val, toOrdered (values ⟨key.val, (Finset.mem_sort _).mp key.property⟩))
    change (decide (RawSyn.ofEntries fields).keys.Nodup && JsonWithBytes.uniqueKeys (RawSyn.ofEntries fields)) = true
    apply Bool.and_eq_true_iff.mpr
    refine ⟨?_, unique_fields fields ?_⟩
    · rw [decide_eq_true_eq, RawSyn.keys_eq_toEntries_fst, RawSyn.toEntries_ofEntries]
      have names : fields.map Prod.fst = keys.sort := by simp [fields, List.map_map, Function.comp_def]
      rw [names]
      exact Finset.sort_nodup _ _
    · intro field member
      obtain ⟨key, _, rfl⟩ := List.mem_map.mp member
      exact ih _

private theorem guard_iff (value : Shallow Cid) :
    ((Drisl.links (toOrdered value)).all (fun
      | .obj cid => cid.val[1]? == some 0x71
      | .blob cid => cid.val[1]? == some 0x55)) = true ↔
    ∀ link ∈ Drisl.links (toOrdered value), ValidLink link := by
  rw [List.all_eq_true]
  constructor <;> intro ok link mem <;> specialize ok link mem <;>
    cases link <;> simpa [ValidLink, IsObjectCid, IsRawCid] using ok

private theorem render_of_valid (value : Shallow Cid)
    (valid : ∀ link ∈ Drisl.links (toOrdered value), ValidLink link) :
    render? value = (if (Drisl.parseCbor? Drisl.i64Cbor cidCodec (canonicalModel value).encode).isSome
      then some (canonicalModel value).encode else none).map List.toByteArray := by
  unfold render?
  dsimp only
  split
  · rfl
  · exact (‹¬_› ((guard_iff value).mpr valid)).elim

theorem roundtrip (value : Shallow Cid)
    (valid : ∀ link ∈ Drisl.links (toOrdered value), ValidLink link)
    (encodable : (canonicalModel value).Encodable)
    (ordered : Drisl.canonicalMaps (canonicalModel value) = true) :
    let bytes := (canonicalModel value).encode.toByteArray
    render? value = some bytes ∧ parse? bytes = some value := by
  let normalized := canonicalOrder (toOrdered value)
  have emitted : Drisl.emitModel Drisl.i64Cbor cidCodec false normalized = canonicalModel value := emit_canonical _ _
  have recovers : ∀ link ∈ Drisl.links normalized, cidCodec.parse? (cidCodec.bytes link) = some link :=
    fun link member => typed_cid_parse_iff.mpr ⟨rfl, valid link ((links_order (toOrdered value)).mem_iff.mp member)⟩
  have laws := Drisl.atproto_ordered_roundtrip_with_codec cidCodec normalized recovers
    (emitted ▸ encodable) (emitted ▸ ordered)
  change render? value = some (canonicalModel value).encode.toByteArray ∧
    parse? (canonicalModel value).encode.toByteArray = some value
  have parsed : Drisl.parseCbor? Drisl.i64Cbor cidCodec (canonicalModel value).encode = some normalized := by
    simpa only [emitted] using laws.2
  constructor
  · simp [render_of_valid value valid, parsed]
  · simp [parse?, parsed, normalized, projection]

theorem parse_render {value : Shallow Cid} {bytes : ByteArray} (encodable : (canonicalModel value).Encodable)
    (rendered : render? value = some bytes) : parse? bytes = some value := by
  have valid : ∀ link ∈ Drisl.links (toOrdered value), ValidLink link := by
    apply (guard_iff value).mp
    unfold render? at rendered
    dsimp only at rendered
    split at rendered
    · assumption
    · contradiction
  have ordered : Drisl.canonicalMaps (canonicalModel value) = true := by
    by_contra bad
    have rejected : Drisl.parseCbor? Drisl.i64Cbor cidCodec (canonicalModel value).encode = none := by
      simp [Drisl.parseCbor?, Cbor.decode_encode _ encodable, bad]
    simp [render_of_valid value valid, rejected] at rendered
  obtain ⟨encoded, parsed⟩ := roundtrip value valid encodable ordered
  exact (Option.some.inj (encoded.symm.trans rendered)) ▸ parsed

theorem reprint {bytes : ByteArray} {value : Shallow Cid} (parsed : parse? bytes = some value) :
    render? value = some bytes ∧ (canonicalModel value).Encodable := by
  obtain ⟨tree, read, rfl⟩ := Option.map_eq_some_iff.mp parsed
  obtain ⟨unique, validLinks⟩ := WireCanonicalReprint.parsed_syntax read
  have normal := WireCanonicalReprint.normalization tree unique
  have model : canonicalModel (lower tree) = Drisl.emitModel Drisl.i64Cbor cidCodec true tree := by
    rw [canonicalModel, ← emit_canonical, normal, emit_canonical]
  have valid : ∀ link ∈ Drisl.links (toOrdered (lower tree)), ValidLink link := by
    intro link hit
    have lifted := (links_order (toOrdered (lower tree))).mem_iff.mpr hit
    rw [normal] at lifted
    exact validLinks link ((links_order tree).mem_iff.mp lifted)
  have cidBytes (input : List UInt8) (link : Link Cid) (parsed : cidCodec.parse? input = some link) :
      cidCodec.bytes link = input := (typed_cid_parse_iff.mp parsed).1
  have emitted := Drisl.atproto_render_of_parse_with_codec cidCodec cidBytes read
  have exactBytes : bytes.data.toList.toByteArray = bytes := by
    apply ByteArray.ext
    simp only [List.data_toByteArray]
  refine ⟨?_, ?_⟩
  · rw [render_of_valid _ valid, model]
    simpa only [Drisl.renderCbor?, exactBytes, Option.map_some] using congrArg (Option.map List.toByteArray) emitted
  · rw [model]
    exact Cbor.encodable_of_decode (Drisl.atproto_model_of_parse_with_codec cidCodec cidBytes read)

end Silmaril.Proofs.Formats.Dasl.WireCanonical
