module

public import Silmaril.Formats.Dasl.Wire.Defs
import Silmaril.Formats.Cbor.Drisl.Number.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl

open Silmaril.Formats.Cbor

theorem i64_roundtrip (bits : UInt64) :
    (Drisl.i64Cbor.readNumber? (Drisl.i64Cbor.number bits.toInt64)).map Int64.toUInt64 = some bits := by
  have signed : Drisl.i64Cbor.readNumber? (Drisl.i64Cbor.number bits.toInt64) = some bits.toInt64 := by
    have parsed := Drisl.int64_toInt bits.toInt64
    cases view : bits.toInt64.toInt <;> simpa [Drisl.i64Cbor, view] using parsed
  simp [signed]

end Silmaril.Proofs.Formats.Dasl

namespace Silmaril.Proofs.Formats.Dasl.Wire

open Silmaril.Formats Silmaril.Formats.Dasl Silmaril.Formats.Dasl.Wire Silmaril.Formats.Cbor

variable {Name : Type}

theorem dictFields_keys (fields : List (String × Shallow Name)) :
    (dictFields fields).1 = (fields.map Prod.fst).toFinset := by
  induction fields with
  | nil => rfl
  | cons entry tail ih => cases entry; simpa [dictFields] using congrArg (insert _) ih

theorem dictFields_value {fields : List (String × Shallow Name)} (distinct : (fields.map Prod.fst).Nodup)
    {entry : String × Shallow Name} (member : entry ∈ fields) :
    (dictFields fields).2 ⟨entry.1, by rw [dictFields_keys]; exact List.mem_toFinset.mpr (List.mem_map_of_mem member)⟩ =
      entry.2 := by
  induction fields with
  | nil => cases member
  | cons head tail ih =>
    obtain ⟨key, value⟩ := head
    have separated := List.nodup_cons.mp distinct
    rcases List.mem_cons.mp member with rfl | inTail
    · simp [dictFields]
    · have inKeys : entry.1 ∈ tail.map Prod.fst := List.mem_map_of_mem inTail
      have different : entry.1 ≠ key := fun same => separated.1 (same ▸ inKeys)
      simp only [dictFields, dite_eq_right different]
      exact ih separated.2 inTail

theorem dictFields_materialize_perm (fields : List (String × Shallow Name)) (distinct : (fields.map Prod.fst).Nodup) :
    ((dictFields fields).1.sort.attach.map (fun key =>
      (key.val, (dictFields fields).2 ⟨key.val, (Finset.mem_sort _).mp key.property⟩))).Perm fields := by
  let dict := dictFields fields
  let materialize : {key : String // key ∈ dict.1.sort} → String × Shallow Name := fun key =>
    (key.val, dict.2 ⟨key.val, (Finset.mem_sort _).mp key.property⟩)
  have find (entry : String × Shallow Name) (member : entry ∈ fields) :
      ∃ key : {key : String // key ∈ dict.1.sort}, materialize key = entry := by
    have inKeys : entry.1 ∈ dict.1 := by
      dsimp only [dict]
      rw [dictFields_keys]
      exact List.mem_toFinset.mpr (List.mem_map_of_mem member)
    refine ⟨⟨entry.1, (Finset.mem_sort _).mpr inKeys⟩, Prod.ext rfl ?_⟩
    exact dictFields_value distinct member
  change (dict.1.sort.attach.map materialize).Perm fields
  have names : (dict.1.sort.attach.map materialize).map Prod.fst = dict.1.sort := by
    simp [List.map_map, Function.comp_def, materialize]
  have enumDistinct : ((dict.1.sort.attach.map materialize).map Prod.fst).Nodup := by
    rw [names]
    exact Finset.sort_nodup _ _
  apply (List.perm_ext_iff_of_nodup enumDistinct.of_map distinct.of_map).mpr
  intro entry
  constructor
  · intro member
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp member
    have inKeys := List.mem_toFinset.mp ((congrArg (fun keys : Finset String => key.val ∈ keys)
      (dictFields_keys fields)).mp ((Finset.mem_sort _).mp key.property))
    obtain ⟨source, present, equal⟩ := List.mem_map.mp inKeys
    obtain ⟨sourceKey, correct⟩ := find source present
    have same : sourceKey = key := Subtype.ext (congrArg Prod.fst correct |>.trans equal)
    exact same ▸ correct.symm ▸ present
  · intro present
    obtain ⟨key, correct⟩ := find entry present
    exact List.mem_map.mpr ⟨key, List.mem_attach _ _, correct⟩

private theorem lower_ofList (children : List (Drisl.OrderedATProto (Link Name))) :
    lower (RawSyn.ofList children) = children.map (lower (index := .val)) := by
  induction children with
  | nil => rfl
  | cons value tail ih => simp [lower, ih]

private theorem lower_ofEntries (fields : List (String × Drisl.OrderedATProto (Link Name))) :
    lower (RawSyn.ofEntries fields) = fields.map (fun entry => (entry.1, lower entry.2)) := by
  induction fields with
  | nil => rfl
  | cons entry tail ih => cases entry; simp [lower, ih]

private theorem dict_congr {left right : Finset String} (same : left = right)
    {values : ↥left → Shallow Name} {others : ↥right → Shallow Name}
    (pointwise : ∀ key : ↥right, values ⟨key.val, same.symm ▸ key.property⟩ = others key) :
    Tree.dict left values = Tree.dict right others := by
  subst right
  exact congrArg (Tree.dict left) (funext pointwise)

theorem lower_map_perm {left right : List (String × Drisl.OrderedATProto (Link Name))}
    (distinct : (left.map Prod.fst).Nodup) (order : left.Perm right) :
    lower (.map (.ofEntries left)) = lower (.map (.ofEntries right)) := by
  let strip (entry : String × Drisl.OrderedATProto (Link Name)) := (entry.1, lower entry.2)
  let leftFields := left.map strip
  let rightFields := right.map strip
  have leftKeys : leftFields.map Prod.fst = left.map Prod.fst := by simp [leftFields, strip, List.map_map]
  have rightKeys : rightFields.map Prod.fst = right.map Prod.fst := by simp [rightFields, strip, List.map_map]
  have swap := order.map strip
  have keySet : (dictFields leftFields).1 = (dictFields rightFields).1 := by
    rw [dictFields_keys, dictFields_keys]
    exact Finset.ext fun _ => List.mem_toFinset.trans ((swap.map Prod.fst).mem_iff.trans List.mem_toFinset.symm)
  rw [lower, lower, lower_ofEntries, lower_ofEntries]
  change Tree.dict (dictFields leftFields).1 (dictFields leftFields).2 =
    Tree.dict (dictFields rightFields).1 (dictFields rightFields).2
  apply dict_congr keySet
  rintro ⟨key, memberKey⟩
  have inRight : key ∈ (rightFields.map Prod.fst).toFinset := dictFields_keys rightFields ▸ memberKey
  obtain ⟨entry, member, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp inRight)
  have leftDistinct : (leftFields.map Prod.fst).Nodup := leftKeys.symm ▸ distinct
  have rightDistinct : (rightFields.map Prod.fst).Nodup := rightKeys.symm ▸ (order.map Prod.fst).nodup_iff.mp distinct
  have fromLeft := dictFields_value leftDistinct (swap.mem_iff.mpr member)
  have fromRight := dictFields_value rightDistinct member
  exact fromLeft.trans fromRight.symm

private theorem lower_fields (keys : Finset String) (values : ↥keys → Shallow Name)
    (ordered : ↥keys → Drisl.OrderedATProto (Link Name)) (recover : ∀ key, lower (ordered key) = values key) :
    (let ⟨fields, payloads⟩ := dictFields (lower (RawSyn.ofEntries (keys.sort.attach.map fun key =>
      (key.val, ordered ⟨key.val, (Finset.mem_sort _).mp key.property⟩))))
     Tree.dict fields payloads) = Tree.dict keys values := by
  rw [lower_ofEntries, List.map_map]
  let fields : List (String × Shallow Name) := keys.sort.attach.map fun key =>
    (key.val, values ⟨key.val, (Finset.mem_sort _).mp key.property⟩)
  have simplify : (keys.sort.attach.map
      ((fun entry : String × Drisl.OrderedATProto (Link Name) => (entry.1, lower entry.2)) ∘
        fun key => (key.val, ordered ⟨key.val, (Finset.mem_sort _).mp key.property⟩))) = fields := by
    simp [fields, Function.comp_def, recover]
  rw [simplify]
  have fieldsKeys : fields.map Prod.fst = keys.sort := by simp [fields, List.map_map, Function.comp_def]
  have keySet : (dictFields fields).1 = keys := by rw [dictFields_keys, fieldsKeys, Finset.sort_toFinset]
  have valuesEq (key : ↥keys) : (dictFields fields).2 ⟨key.val, keySet.symm ▸ key.property⟩ = values key := by
    have distinct : (fields.map Prod.fst).Nodup := fieldsKeys.symm ▸ Finset.sort_nodup _ _
    have entry : (key.val, values key) ∈ fields :=
      List.mem_map_of_mem (List.mem_attach _ ⟨key.val, (Finset.mem_sort _).mpr key.property⟩)
    exact dictFields_value distinct entry
  change Tree.dict (dictFields fields).1 (dictFields fields).2 = Tree.dict keys values
  exact dict_congr keySet valuesEq

private theorem list_congr {left right : Nat} (same : left = right)
    {values : Fin left → Shallow Name} {others : Fin right → Shallow Name}
    (pointwise : ∀ index, values index = others (Fin.cast same index)) :
    Tree.list left values = Tree.list right others := by
  subst right
  exact congrArg (Tree.list left) (funext pointwise)

theorem lower_toOrdered (value : Shallow Name) : lower (toOrdered value) = value := by
  induction value with
  | ref _ => rfl
  | obj impossible _ _ | blob impossible _ => exact impossible.elim
  | i64 _ => simp [toOrdered, lower]
  | bytes payload =>
    simp only [toOrdered, lower, Tree.bytes.injEq]
    apply ByteArray.ext
    simp
  | string _ | bool _ | null => rfl
  | list len children ih =>
    change (fun items : List (Shallow Name) => Tree.list items.length items.get)
      (lower (RawSyn.ofList (List.ofFn fun index => toOrdered (children index)))) = _
    have recovered : lower (RawSyn.ofList (List.ofFn fun index => toOrdered (children index))) = List.ofFn children := by
      rw [lower_ofList, List.map_ofFn]
      exact congrArg List.ofFn (funext ih)
    rw [recovered]
    exact list_congr List.length_ofFn (List.get_ofFn children)
  | dict keys values ih => exact lower_fields keys values _ ih

theorem typed_cid_roundtrip {link : Link Cid} (valid : ValidLink link) :
    cidCodec.parse? (cidCodec.bytes link) = some link := by
  cases link with
  | obj cid =>
    have tag : IsObjectCid cid := valid
    simp [cidCodec, Drisl.Cid.codec, cid.property, bind, IsObjectCid] at tag ⊢
    exact tag
  | blob cid =>
    have tag : IsRawCid cid := valid
    have different : (0x55 : UInt8) ≠ 0x71 := by decide
    simp [cidCodec, Drisl.Cid.codec, cid.property, bind, IsRawCid] at tag ⊢
    simp [tag, different]

theorem typed_cid_parse {bytes : List UInt8} {link : Link Cid} (parsed : cidCodec.parse? bytes = some link) :
    cidCodec.bytes link = bytes ∧ ValidLink link := by
  obtain ⟨cid, read, classified⟩ := Option.bind_eq_some_iff.mp parsed
  have source : cid.val = bytes := by
    simp only [Drisl.Cid.codec] at read
    split at read
    · cases Option.some.inj read; rfl
    · contradiction
  split at classified
  · cases Option.some.inj classified; exact ⟨source, by assumption⟩
  · split at classified
    · cases Option.some.inj classified; exact ⟨source, by assumption⟩
    · contradiction

theorem parse_eq_some_iff {bytes : ByteArray} {tree : Shallow Cid} :
    parse? bytes = some tree ↔
      ∃ value ordered, Cbor.decode bytes.data.toList = some value ∧ value.encode = bytes.data.toList ∧
        Drisl.canonicalMaps value = true ∧ Drisl.interpretCbor? Drisl.i64Cbor cidCodec value = some ordered ∧
        lower ordered = tree := by
  rw [parse?, Option.map_eq_some_iff]
  constructor
  · rintro ⟨ordered, parsed, rfl⟩
    change (Cbor.decode bytes.data.toList).bind _ = _ at parsed
    obtain ⟨value, decoded, checked⟩ := Option.bind_eq_some_iff.mp parsed
    split at checked
    · rename_i canonical
      exact ⟨value, ordered, decoded, canonical.1, canonical.2, checked, rfl⟩
    · contradiction
  · rintro ⟨value, ordered, decoded, exactBytes, order, accepted, rfl⟩
    refine ⟨ordered, ?_, rfl⟩
    change (Cbor.decode bytes.data.toList).bind _ = _
    have canonical : value.encode = bytes.data.toList ∧ Drisl.canonicalMaps value = true := ⟨exactBytes, order⟩
    exact Option.bind_eq_some_iff.mpr ⟨value, decoded, by simpa only [ite_eq_left canonical] using accepted⟩

end Silmaril.Proofs.Formats.Dasl.Wire
