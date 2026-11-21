module

public import Silmaril.Formats.Dasl.Wire.Canonical.Defs
public import Silmaril.Formats.Dasl.Wire.Thms
public import Silmaril.Formats.Cbor.Drisl.Model.Thms
public import Silmaril.Formats.Cbor.Value.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl.WireCanonicalReprint

open Silmaril.Formats Silmaril.Formats.Cbor Silmaril.Formats.Dasl Silmaril.Formats.Dasl.Wire

variable {Name : Type}

private theorem head_length_mono (major : Nat) : Monotone (fun count => (encodeHead major count).length) := by
  intro left right order
  dsimp only [encodeHead]
  repeat' split
  all_goals simp [beBytes]
  all_goals omega

private theorem encoded_key_inj {left right : String}
    (same : (Drisl.utf8Value left).encode = (Drisl.utf8Value right).encode) : left = right := by
  have lengths := congrArg List.length same
  simp only [Drisl.utf8Value, Value.encode, List.length_append] at lengths
  have sameLength : left.toUTF8.data.toList.length = right.toUTF8.data.toList.length := by
    rcases lt_trichotomy left.toUTF8.data.toList.length right.toUTF8.data.toList.length with less | equal | greater
    · have compareHeads := head_length_mono 3 less.le
      dsimp only at compareHeads
      omega
    · exact equal
    · have compareHeads := head_length_mono 3 greater.le
      dsimp only at compareHeads
      omega
  simp only [Drisl.utf8Value, Value.encode, sameLength, List.append_cancel_left_eq] at same
  exact String.toByteArray_inj.mp (ByteArray.ext (Array.toList_inj.mp same))

private theorem keyLE_iff (left right : String) : keyLE left right = true ↔
    (Drisl.utf8Value left).encode ≤ (Drisl.utf8Value right).encode := by
  simp only [keyLE, Bool.not_eq_true', ← Bool.not_eq_true, Drisl.lexLt_iff]
  rfl

private theorem key_sort_perm {Payload : Type} {left right : List (String × Payload)}
    (distinct : (left.map Prod.fst).Nodup) (perm : left.Perm right) :
    left.mergeSort (fun left right => keyLE left.1 right.1) = right.mergeSort (fun left right => keyLE left.1 right.1) := by
  let precedes := fun left right : String × Payload => keyLE left.1 right.1
  have ordered := List.pairwise_mergeSort (le := precedes)
    (fun a b c hab hbc => (keyLE_iff _ _).mpr (List.le_trans ((keyLE_iff _ _).mp hab) ((keyLE_iff _ _).mp hbc)))
    (fun a b => Bool.or_eq_true_iff.mpr ((List.le_total _ _).imp ((keyLE_iff _ _).mpr) ((keyLE_iff _ _).mpr)))
  apply List.Perm.eq_of_pairwise _ (ordered left) (ordered right)
    ((List.mergeSort_perm left precedes).trans (perm.trans (List.mergeSort_perm right precedes).symm))
  intro first second inLeft inRight forward backward
  have sameKey := encoded_key_inj (List.le_antisymm ((keyLE_iff _ _).mp forward) ((keyLE_iff _ _).mp backward))
  exact List.inj_on_of_nodup_map distinct ((List.mergeSort_perm left precedes).mem_iff.mp inLeft)
    (perm.mem_iff.mpr ((List.mergeSort_perm right precedes).mem_iff.mp inRight)) sameKey

private def liftLower : {index : JsonIx} → RawSyn String (Drisl.Scalar Int64 (Link Name)) index →
    RawSyn String (Drisl.Scalar Int64 (Link Name)) index
  | .val, input => toOrdered (lower input)
  | .arr, input => .ofList ((lower input).map toOrdered)
  | .obj, input => .ofEntries ((lower input).map (fun entry => (entry.1, toOrdered entry.2)))

private theorem canon_entries : (fields : RawSyn String (Drisl.Scalar Int64 (Link Name)) .obj) →
    (canonicalOrder fields).toEntries = fields.toEntries.map (fun entry => (entry.1, canonicalOrder entry.2))
  | .objNil => by simp [canonicalOrder]
  | .objCons _ _ tail => by simp [canonicalOrder, canon_entries tail]

private theorem lower_names : (fields : RawSyn String (Drisl.Scalar Int64 (Link Name)) .obj) →
    (lower fields).map Prod.fst = fields.keys
  | .objNil => by simp [lower]
  | .objCons _ _ tail => by simp [lower, lower_names tail]

private theorem canonical_lift_lower {index : JsonIx} (input : RawSyn String (Drisl.Scalar Int64 (Link Name)) index)
    (unique : JsonWithBytes.uniqueKeys input = true) : canonicalOrder (liftLower input) = canonicalOrder input := by
  induction input with
  | scalar atom =>
    cases atom with
    | link link => rfl
    | data payload =>
      cases payload <;> simp [liftLower, lower, toOrdered, canonicalOrder]
  | nil | objNil => rfl
  | cons head tail headEq tailEq | objCons _ head tail headEq tailEq =>
    obtain ⟨headUnique, tailUnique⟩ := Bool.and_eq_true_iff.mp unique
    have headSame := headEq headUnique
    have tailSame := tailEq tailUnique
    simpa only [liftLower, lower, List.map_cons, RawSyn.ofList, RawSyn.ofEntries, canonicalOrder] using
      congrArg₂ _ headSame tailSame
  | list items ih =>
    have asList : (List.ofFn (lower items).get) = lower items := List.ofFn_getElem
    have mapped : (List.ofFn (fun index => toOrdered ((lower items).get index))) = (lower items).map toOrdered :=
      (List.map_ofFn (f := (lower items).get) (g := toOrdered)).symm.trans (congrArg (List.map toOrdered) asList)
    rw [liftLower, lower, toOrdered, mapped]
    simp only [canonicalOrder, RawSyn.list.injEq]
    exact ih unique
  | map fields ih =>
    obtain ⟨keysUnique, fieldsUnique⟩ := Bool.and_eq_true_iff.mp unique
    have distinct : ((lower fields).map Prod.fst).Nodup := lower_names fields ▸ of_decide_eq_true keysUnique
    let dict := dictFields (lower fields)
    let liftField := fun entry : String × Shallow Name => (entry.1, toOrdered entry.2)
    let entries := dict.1.sort.attach.map (fun key =>
      (key.val, dict.2 ⟨key.val, (Finset.mem_sort _).mp key.property⟩))
    have liftPerm := (dictFields_materialize_perm (lower fields) distinct).map liftField
    have normalizedPrelim : (canonicalOrder (.ofEntries (entries.map liftField))).toEntries.Perm
        (canonicalOrder (liftLower fields)).toEntries := by
      simp only [canon_entries, liftLower, RawSyn.toEntries_ofEntries]
      exact liftPerm.map (fun entry => (entry.1, canonicalOrder entry.2))
    rw [ih fieldsUnique] at normalizedPrelim
    have normalizedDistinct : ((canonicalOrder fields).toEntries.map Prod.fst).Nodup := by
      simpa [canon_entries, List.map_map, Function.comp_def, ← RawSyn.keys_eq_toEntries_fst] using
        (of_decide_eq_true keysUnique : fields.keys.Nodup)
    have materialized : liftLower (.map fields) = .map (.ofEntries (entries.map liftField)) := by
      simp only [liftLower, lower, toOrdered, entries, List.map_map, liftField, Function.comp_def, dict]
    rw [materialized]
    rw [canonicalOrder, canonicalOrder, key_sort_perm normalizedDistinct normalizedPrelim.symm]

private theorem read_link {value : Cbor.Value} {link : Link Cid}
    (read : Drisl.readCborLeaf? Drisl.i64Cbor cidCodec value = some (.link link)) : ValidLink link := by
  unfold Drisl.readCborLeaf? at read
  split at read <;> simp only [Functor.map, Option.map_eq_some_iff, Function.comp_apply,
    Option.some.injEq, reduceCtorEq, and_false, exists_false] at read
  obtain ⟨decoded, parsed, same⟩ := read
  cases same
  exact (typed_cid_parse_iff.mp parsed).2

private def LinksValid {index : JsonIx} (tree : RawSyn String (Drisl.Scalar Int64 (Link Cid)) index) : Prop :=
  ∀ link ∈ Drisl.links tree, ValidLink link

mutual

private theorem model_links (value : Cbor.Value) (tree : Drisl.OrderedATProto (Link Cid))
    (read : Drisl.readModel? Drisl.i64Cbor cidCodec value = some tree) : LinksValid tree := by
  cases value <;> simp [Drisl.readModel?, Option.map_eq_some_iff] at read
  all_goals obtain ⟨child, readChild, rfl⟩ := read
  case array => exact items_links _ _ readChild
  case map => exact fields_links _ _ readChild
  all_goals
    intro link hit
    cases child with
    | data _ => simp [Drisl.links, RawSyn.scalars] at hit
    | link expected =>
      have same : link = expected := by simpa [Drisl.links, RawSyn.scalars] using hit
      subst expected
      exact read_link readChild

private theorem items_links (items : List Cbor.Value) (tree : RawSyn String (Drisl.Scalar Int64 (Link Cid)) .arr)
    (read : Drisl.readItems? Drisl.i64Cbor cidCodec items = some tree) : LinksValid tree := by
  cases items with
  | nil => cases Option.some.inj read; simp [LinksValid, Drisl.links, RawSyn.scalars]
  | cons value rest =>
    obtain ⟨head, readHead, tail, readTail, rfl⟩ := by simpa [Drisl.readItems?, Option.bind_eq_some_iff] using read
    have headValid := model_links _ _ readHead
    have tailValid := items_links _ _ readTail
    intro link hit
    simp only [Drisl.links, RawSyn.scalars, List.filterMap_append, List.mem_append] at hit
    exact hit.elim (headValid link) (tailValid link)

private theorem fields_links (entries : List (Cbor.Value × Cbor.Value))
    (tree : RawSyn String (Drisl.Scalar Int64 (Link Cid)) .obj)
    (read : Drisl.readEntries? Drisl.i64Cbor cidCodec entries = some tree) : LinksValid tree := by
  cases entries with
  | nil => cases Option.some.inj read; simp [LinksValid, Drisl.links, RawSyn.scalars]
  | cons entry rest =>
    obtain ⟨key, value⟩ := entry
    cases key <;> simp [Drisl.readEntries?, Option.bind_eq_some_iff] at read
    obtain ⟨name, _, head, readHead, tail, readTail, rfl⟩ := read
    have headValid := model_links _ _ readHead
    have tailValid := fields_links _ _ readTail
    intro link hit
    simp only [Drisl.links, RawSyn.scalars, List.filterMap_append, List.mem_append] at hit
    exact hit.elim (headValid link) (tailValid link)

end

theorem parsed_syntax {bytes : List UInt8} {tree : Drisl.OrderedATProto (Link Cid)}
    (read : Drisl.parseCbor? Drisl.i64Cbor cidCodec bytes = some tree) :
    JsonWithBytes.uniqueKeys tree = true ∧ ∀ link ∈ Drisl.links tree, ValidLink link := by
  obtain ⟨model, _, _, _, interpreted⟩ := (Drisl.parseCbor_eq_some_iff _ _).mp read
  obtain ⟨ordered, readOrdered, checked⟩ := Option.bind_eq_some_iff.mp interpreted
  split at checked
  · obtain rfl := Option.some.inj checked
    exact ⟨by assumption, model_links _ _ readOrdered⟩
  · contradiction

theorem normalization (input : Drisl.OrderedATProto (Link Name))
    (unique : JsonWithBytes.uniqueKeys input = true) :
    canonicalOrder (toOrdered (lower input)) = canonicalOrder input := canonical_lift_lower input unique

end Silmaril.Proofs.Formats.Dasl.WireCanonicalReprint
