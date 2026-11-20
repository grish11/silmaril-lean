module

public import Silmaril.Formats.Cbor.Drisl.Model.Defs
import Silmaril.Formats.Cbor.Drisl.Thms
import Silmaril.Formats.Cbor.Drisl.Cid.Thms
import Silmaril.Formats.Cbor.Drisl.Number.Thms
import Silmaril.Formats.Utf8.Thms

public section

namespace Silmaril.Proofs.Formats.Cbor.Drisl.Model

open Silmaril.Formats Silmaril.Formats.Cbor Silmaril.Formats.Cbor.Drisl

private theorem lexLt_iff (left right : List UInt8) :
    lexLt left right = true ↔ List.Lex (· < ·) left right := by
  induction left generalizing right <;> cases right <;>
    simp_all [lexLt, List.cons_lex_cons_iff]

private theorem sorted_pairwise (keys : List (List UInt8)) (h : strictlySorted keys = true) :
    keys.Pairwise (List.Lex (· < ·)) := by
  induction keys with
  | nil => simp
  | cons first rest ih =>
    cases rest with
    | nil => simp
    | cons second tail =>
      obtain ⟨before, sorted⟩ := Bool.and_eq_true_iff.mp h
      have pairwise := ih sorted
      refine List.Pairwise.cons ?_ pairwise
      intro key member
      have order := (lexLt_iff _ _).mp before
      rcases List.mem_cons.mp member with rfl | member
      · exact order
      · exact List.lex_trans (r := fun a b : UInt8 => a < b) (fun left right => UInt8.lt_trans left right)
          order ((List.pairwise_cons.mp pairwise).1 key member)

private theorem sorted_nodup (keys : List (List UInt8)) (h : strictlySorted keys = true) :
    keys.Nodup := by
  apply (sorted_pairwise keys h).imp
  intro left right order same
  subst right
  exact List.lex_irrefl (fun _ => UInt8.lt_irrefl _) _ order

private theorem utf8_eq_of_read {bytes : List UInt8} {name : String}
    (read : String.fromUTF8? bytes.toByteArray = some name) : bytes = name.toByteArray.data.toList := by
  have same := Utf8.fromUTF8?_eq_some read
  rw [List.data_toByteArray, List.toList_toArray] at same
  rw [same, ← String.utf8Encode_toList]
  simp [List.utf8Encode, Utf8.encode]

private theorem readEntries_keys {Numeric Link : Type} (numeric : CborCodec Numeric)
    (cid : CidCodec Link) (entries : List (Value × Value))
    (tree : RawSyn String (Scalar Numeric Link) .obj)
    (read : readEntries? numeric cid entries = some tree) :
    tree.keys.map (Value.encode ∘ utf8Value) = entries.map (fun entry => entry.1.encode) := by
  induction entries generalizing tree with
  | nil => cases Option.some.inj read; simp
  | cons entry rest ih =>
    obtain ⟨key, value⟩ := entry
    cases key <;> simp [readEntries?, Option.bind_eq_some_iff] at read
    rename_i bytes
    obtain ⟨name, text, valueTree, parsed, tail, readTail, rfl⟩ := read
    simp [utf8Value, utf8_eq_of_read text, ih _ readTail]

mutual

private theorem readModel_unique {Numeric Link : Type} (numeric : CborCodec Numeric)
    (cid : CidCodec Link) (value : Value) (tree : RawJson (Scalar Numeric Link))
    (read : readModel? numeric cid value = some tree) (sorted : canonicalMaps value = true) :
    JsonWithBytes.uniqueKeys tree = true := by
  cases value <;> simp [readModel?, Option.map_eq_some_iff] at read
  all_goals obtain ⟨child, readChild, rfl⟩ := read
  all_goals try rfl
  · exact readItems_unique numeric cid _ _ readChild sorted
  · obtain ⟨order, children⟩ := Bool.and_eq_true_iff.mp sorted
    have keyNoDup : child.keys.Nodup := by
      apply List.Nodup.of_map (f := Value.encode ∘ utf8Value)
      rw [readEntries_keys numeric cid _ _ readChild]
      exact sorted_nodup _ order
    simp [JsonWithBytes.uniqueKeys, keyNoDup, readEntries_unique numeric cid _ _ readChild children]

private theorem readItems_unique {Numeric Link : Type} (numeric : CborCodec Numeric)
    (cid : CidCodec Link) (items : List Value) (tree : RawSyn String (Scalar Numeric Link) .arr)
    (read : readItems? numeric cid items = some tree) (sorted : canonicalItems items = true) :
    JsonWithBytes.uniqueKeys tree = true := by
  cases items with
  | nil => cases Option.some.inj read; rfl
  | cons value rest =>
    obtain ⟨head, readHead, tail, readTail, rfl⟩ := by
      simpa [readItems?, Option.bind_eq_some_iff] using read
    obtain ⟨headSorted, tailSorted⟩ := Bool.and_eq_true_iff.mp sorted
    simp [JsonWithBytes.uniqueKeys, readModel_unique numeric cid _ _ readHead headSorted,
      readItems_unique numeric cid _ _ readTail tailSorted]

private theorem readEntries_unique {Numeric Link : Type} (numeric : CborCodec Numeric)
    (cid : CidCodec Link) (entries : List (Value × Value))
    (tree : RawSyn String (Scalar Numeric Link) .obj)
    (read : readEntries? numeric cid entries = some tree) (sorted : canonicalEntries entries = true) :
    JsonWithBytes.uniqueKeys tree = true := by
  cases entries with
  | nil => cases Option.some.inj read; rfl
  | cons entry rest =>
    obtain ⟨key, value⟩ := entry
    cases key <;> simp [readEntries?, Option.bind_eq_some_iff] at read
    obtain ⟨name, _, head, readHead, tail, readTail, rfl⟩ := read
    obtain ⟨headSorted, tailSorted⟩ := Bool.and_eq_true_iff.mp sorted
    simp [JsonWithBytes.uniqueKeys, readModel_unique numeric cid _ _ readHead headSorted,
      readEntries_unique numeric cid _ _ readTail tailSorted]

end

theorem interpret_of_sorted {Numeric Link : Type} (numeric : CborCodec Numeric)
    (cid : CidCodec Link) (value : Value) (sorted : canonicalMaps value = true) :
    interpretCbor? numeric cid value = readModel? numeric cid value := by
  unfold interpretCbor?
  cases read : readModel? numeric cid value with
  | none => rfl
  | some tree => simp [readModel_unique numeric cid _ _ read sorted]

private def isLeaf : Value → Prop
  | .array _ | .map _ => False
  | _ => True

private theorem utf8_check (bytes : List UInt8) :
    Utf8.isWellFormed bytes = true ↔ (String.fromUTF8? bytes.toByteArray).isSome := by
  rw [Utf8.isWellFormed_iff, Utf8.fromUTF8?_isSome_iff, List.data_toByteArray, List.toList_toArray]

private theorem fixed_leaf (rule : LinkRule) (profile : CidProfile)
    (links : ∀ bytes, profile.accepts bytes = cidOk .exact rule (0 :: bytes))
    (value : Value) (encodable : value.Encodable) (leaf : isLeaf value) :
    (ok ⟨true, false, .exact, rule⟩ value = true ↔
      (readCborLeaf? drislCbor (Cid.codec profile) value).isSome) ∧
    (ok ⟨false, true, .exact, rule⟩ value = true ↔
      (readCborLeaf? i64Cbor (Cid.codec profile) value).isSome) := by
  cases value with
  | array | map => exact leaf.elim
  | uint amount | nint amount =>
    simp [ok, okInt, readCborLeaf?, drislCbor, i64Cbor, Integer.ofInt?, int64?]
    omega
  | bytes bytes => simp [Value.Encodable] at encodable; simp [ok, encodable, readCborLeaf?]
  | text bytes =>
    simp [Value.Encodable] at encodable
    simp [ok, encodable, readCborLeaf?, utf8_check]
  | simple number =>
    by_cases falseValue : number = 20
    · subst number; simp [ok, readCborLeaf?]
    by_cases trueValue : number = 21
    · subst number; simp [ok, readCborLeaf?]
    by_cases nullValue : number = 22
    · subst number; simp [ok, readCborLeaf?]
    simp [ok, falseValue, trueValue, nullValue, readCborLeaf?, drislCbor, i64Cbor]
  | float width bits =>
    by_cases eight : width = 8
    · subst width; simp [ok, readCborLeaf?, drislCbor, i64Cbor]
    · simp [ok, eight, readCborLeaf?, drislCbor, i64Cbor]
  | tag tag content =>
    by_cases isLink : tag = 42
    · subst tag
      cases content <;> simp [ok, readCborLeaf?, drislCbor, i64Cbor]
      rename_i bytes
      have bounded := encodable.2
      change bytes.length < 2 ^ 64 at bounded
      cases bytes with
      | nil => simp [cidOk]
      | cons first tail =>
        by_cases zero : first = 0
        · subst first
          change tail.length + 1 < 18446744073709551616 at bounded
          simp [bounded, Cid.codec, links]
        · simp [cidOk, zero]
    · cases content <;> simp [ok, readCborLeaf?, drislCbor, i64Cbor, isLink]

private theorem isSome_bind_const {A B C : Type} (first : Option A) (second : Option B)
    (pair : A → B → C) :
    (first.bind fun head => second.bind fun tail => some (pair head tail)).isSome =
      (first.isSome && second.isSome) := by
  cases first <;> cases second <;> rfl

section Compatibility

variable {Numeric Link : Type} (numeric : CborCodec Numeric) (cid : CidCodec Link) (profile : Profile)

private def LeafAgreement : Prop := ∀ value, value.Encodable → isLeaf value →
  (ok profile value = true ↔ (readCborLeaf? numeric cid value).isSome)

mutual

private theorem model_ok (leaf : LeafAgreement numeric cid profile) (value : Value)
    (encodable : value.Encodable) :
    ok profile value = true ↔ canonicalMaps value = true ∧ (readModel? numeric cid value).isSome := by
  cases value with
  | array items =>
    obtain ⟨bounded, children⟩ := encodable
    change items.length < 18446744073709551616 at bounded
    simpa [ok, bounded, canonicalMaps, readModel?] using items_ok leaf items children
  | map entries =>
    obtain ⟨bounded, children⟩ := encodable
    change entries.length < 18446744073709551616 at bounded
    simp [ok, bounded, canonicalMaps, readModel?, entries_ok leaf entries children]
    tauto
  | uint | nint | bytes | text | simple | float | tag =>
    simpa [canonicalMaps, readModel?] using leaf _ encodable trivial

private theorem items_ok (leaf : LeafAgreement numeric cid profile) (items : List Value)
    (encodable : ListEncodable items) :
    okList profile items = true ↔ canonicalItems items = true ∧ (readItems? numeric cid items).isSome := by
  cases items with
  | nil => simp [okList, canonicalItems, readItems?]
  | cons value tail =>
    obtain ⟨head, rest⟩ := encodable
    simp only [okList, canonicalItems, readItems?, Bool.and_eq_true, bind, pure]
    rw [isSome_bind_const, Bool.and_eq_true, model_ok leaf value head, items_ok leaf tail rest]
    tauto

private theorem entries_ok (leaf : LeafAgreement numeric cid profile) (entries : List (Value × Value))
    (encodable : MapEncodable entries) :
    okMap profile entries = true ↔
      canonicalEntries entries = true ∧ (readEntries? numeric cid entries).isSome := by
  cases entries with
  | nil => simp [okMap, canonicalEntries, readEntries?]
  | cons entry tail =>
    obtain ⟨key, value⟩ := entry
    obtain ⟨keyBound, head, rest⟩ := encodable
    cases key <;> simp [okMap, isText, readEntries?]
    rename_i bytes
    change bytes.length < 2 ^ 64 at keyBound
    simp only [ok, keyBound, decide_true, Bool.true_and, canonicalEntries, Bool.and_eq_true, utf8_check]
    rw [model_ok leaf value head, entries_ok leaf tail rest]
    cases String.fromUTF8? bytes.toByteArray <;> simp [isSome_bind_const]
    tauto

end

private theorem model_membership (leaf : LeafAgreement numeric cid profile) (value : Value)
    (encodable : value.Encodable) :
    ok profile value = true ↔ canonicalMaps value = true ∧ value ∈ cborValues numeric cid := by
  rw [model_ok numeric cid profile leaf value encodable]
  apply and_congr_right
  intro order
  change _ ↔ (interpretCbor? numeric cid value).isSome
  rw [interpret_of_sorted numeric cid value order]

end Compatibility

private theorem language_eq {Numeric Link : Type} (numeric : CborCodec Numeric) (cid : CidCodec Link)
    (profile : Profile) (leaf : LeafAgreement numeric cid profile) :
    canonicalCbor numeric cid = language profile := by
  ext bytes
  rw [← check_iff]
  change (parseCbor? numeric cid bytes).isSome = true ↔ check profile bytes = true
  cases read : Cbor.decode bytes with
  | none => simp [parseCbor?, check, read]
  | some value =>
    simp only [parseCbor?, check, read, Bool.and_eq_true, beq_iff_eq]
    rw [model_membership numeric cid profile leaf value (encodable_of_decode read)]
    change (if value.encode = bytes ∧ canonicalMaps value = true then interpretCbor? numeric cid value
      else none).isSome = true ↔
      (canonicalMaps value = true ∧ (interpretCbor? numeric cid value).isSome = true) ∧ value.encode = bytes
    by_cases valid : value.encode = bytes ∧ canonicalMaps value = true <;> simp [valid]
    tauto

theorem drisl_dasl_language : drislCborLanguage .dasl = language .drislExactCid :=
  language_eq _ _ _ fun value bounded leaf => (fixed_leaf .dasl .dasl (fun _ => rfl) value bounded leaf).1

theorem drisl_bdasl_language : drislCborLanguage .bdasl = language .drislBdaslExactCid :=
  language_eq _ _ _ fun value bounded leaf => (fixed_leaf .bdasl .bdasl (fun _ => rfl) value bounded leaf).1

theorem atproto_dasl_language : atprotoCborLanguage .dasl = language .atprotoCoreExactCid :=
  language_eq _ _ _ fun value bounded leaf => (fixed_leaf .dasl .dasl (fun _ => rfl) value bounded leaf).2

theorem atproto_bdasl_language : atprotoCborLanguage .bdasl =
    language { Profile.atprotoCoreExactCid with links := .bdasl } :=
  language_eq _ _ _ fun value bounded leaf => (fixed_leaf .bdasl .bdasl (fun _ => rfl) value bounded leaf).2

private theorem sort_eq_of_sorted (entries : List (Value × Value))
    (sorted : strictlySorted (entries.map fun entry => entry.1.encode) = true) :
    entries.mergeSort (fun left right => !lexLt right.1.encode left.1.encode) = entries := by
  apply List.mergeSort_of_pairwise
  have ordered : entries.Pairwise (fun left right => List.Lex (· < ·) left.1.encode right.1.encode) :=
    List.pairwise_map.mp (sorted_pairwise _ sorted)
  apply ordered.imp
  intro left right order
  simp only [Bool.not_eq_true', ← Bool.not_eq_true, lexLt_iff]
  exact fun reverse => List.lex_irrefl (fun _ => UInt8.lt_irrefl _) _
    (List.lex_trans (fun a b => UInt8.lt_trans a b) order reverse)

section Reencode

variable {Numeric Link : Type} (numeric : CborCodec Numeric) (cid : CidCodec Link)

private def LeafReencode : Prop := ∀ value leaf, readCborLeaf? numeric cid value = some leaf →
  emitLeaf numeric cid leaf = value

mutual

private theorem emit_readModel (leafLaw : LeafReencode numeric cid) (value : Value)
    (tree : RawJson (Scalar Numeric Link)) (read : readModel? numeric cid value = some tree)
    (sorted : canonicalMaps value = true) : emitModel numeric cid true tree = value := by
  cases value <;> simp [readModel?, Option.map_eq_some_iff] at read
  all_goals obtain ⟨child, readChild, rfl⟩ := read
  all_goals try exact leafLaw _ _ readChild
  · simp [emitModel, emit_readItems leafLaw _ _ readChild sorted]
  · obtain ⟨order, children⟩ := Bool.and_eq_true_iff.mp sorted
    simp [emitModel, emit_readEntries leafLaw _ _ readChild children, sort_eq_of_sorted _ order]

private theorem emit_readItems (leafLaw : LeafReencode numeric cid) (items : List Value)
    (tree : RawSyn String (Scalar Numeric Link) .arr) (read : readItems? numeric cid items = some tree)
    (sorted : canonicalItems items = true) : emitModel numeric cid true tree = items := by
  cases items with
  | nil => cases Option.some.inj read; rfl
  | cons value rest =>
    obtain ⟨head, readHead, tail, readTail, rfl⟩ := by simpa [readItems?, Option.bind_eq_some_iff] using read
    obtain ⟨headSorted, tailSorted⟩ := Bool.and_eq_true_iff.mp sorted
    simp [emitModel, emit_readModel leafLaw _ _ readHead headSorted, emit_readItems leafLaw _ _ readTail tailSorted]

private theorem emit_readEntries (leafLaw : LeafReencode numeric cid) (entries : List (Value × Value))
    (tree : RawSyn String (Scalar Numeric Link) .obj)
    (read : readEntries? numeric cid entries = some tree) (sorted : canonicalEntries entries = true) :
    emitModel numeric cid true tree = entries := by
  cases entries with
  | nil => cases Option.some.inj read; rfl
  | cons entry rest =>
    obtain ⟨key, value⟩ := entry
    cases key <;> simp [readEntries?, Option.bind_eq_some_iff] at read
    obtain ⟨name, text, head, readHead, tail, readTail, rfl⟩ := read
    obtain ⟨headSorted, tailSorted⟩ := Bool.and_eq_true_iff.mp sorted
    simp [emitModel, utf8Value, utf8_eq_of_read text, emit_readModel leafLaw _ _ readHead headSorted,
      emit_readEntries leafLaw _ _ readTail tailSorted]

end

theorem render_of_parse (leafLaw : ∀ value leaf, readCborLeaf? numeric cid value = some leaf →
    emitLeaf numeric cid leaf = value) (bytes : List UInt8) (tree : RawJson (Scalar Numeric Link))
    (read : parseCbor? numeric cid bytes = some tree) : renderCbor? numeric cid tree = some bytes := by
  have wireRead := read
  unfold parseCbor? at read
  obtain ⟨value, _, accepted⟩ := Option.bind_eq_some_iff.mp read
  split at accepted
  · rename_i canonical
    rw [interpret_of_sorted numeric cid value canonical.2] at accepted
    have emitted := emit_readModel numeric cid leafLaw value tree accepted canonical.2
    simp [renderCbor?, emitted, canonical.1, wireRead]
  · contradiction

end Reencode

private theorem leaf_reencode {Numeric Link : Type} (numeric : CborCodec Numeric) (cid : CidCodec Link)
    (readNumber : ∀ value number, numeric.readNumber? value = some number → numeric.number number = value)
    (readCid : ∀ bytes link, cid.parse? bytes = some link → cid.bytes link = bytes) :
    LeafReencode numeric cid := by
  intro value leaf read
  unfold readCborLeaf? at read
  split at read
  · cases Option.some.inj read; rfl
  · cases Option.some.inj read; rfl
  · cases Option.some.inj read; rfl
  · cases Option.some.inj read; rfl
  · obtain ⟨name, text, rfl⟩ := Option.map_eq_some_iff.mp read
    simp [emitLeaf, utf8Value, utf8_eq_of_read text]
  · obtain ⟨link, parsed, rfl⟩ := Option.map_eq_some_iff.mp read
    simp [emitLeaf, readCid _ _ parsed]
  · obtain ⟨number, parsed, rfl⟩ := Option.map_eq_some_iff.mp read
    exact readNumber _ _ parsed

private theorem cid_reencode (profile : CidProfile) (bytes : List UInt8) (link : Cid profile)
    (read : (Cid.codec profile).parse? bytes = some link) : (Cid.codec profile).bytes link = bytes := by
  simp only [Cid.codec] at read
  split at read
  · cases Option.some.inj read; rfl
  · contradiction

private theorem drisl_number_reencode (value : Value) (number : Number)
    (read : drislCbor.readNumber? value = some number) : drislCbor.number number = value := by
  simp only [drislCbor] at read
  split at read
  · rename_i amount
    simp only [Integer.ofInt?] at read
    split at read
    · cases Option.some.inj read
      have bound : amount < UInt64.size := by assumption
      simp [drislCbor, Integer.toCbor, UInt64.toNat_ofNat', Nat.mod_eq_of_lt bound]
    · contradiction
  · rename_i amount
    simp only [Integer.ofInt?] at read
    split at read
    · cases Option.some.inj read
      have bound : amount < UInt64.size := by assumption
      simp [drislCbor, Integer.toCbor, UInt64.toNat_ofNat', Nat.mod_eq_of_lt bound]
    · contradiction
  · split at read
    · cases Option.some.inj read; rfl
    · contradiction
  · contradiction

private theorem int64_read_toInt (value : Int) (number : Int64)
    (read : int64? value = some number) : number.toInt = value := by
  unfold int64? at read
  split at read
  · rename_i range
    cases Option.some.inj read
    exact Int64.toInt_ofInt_of_le range.1 range.2
  · contradiction

private theorem atproto_number_reencode (value : Value) (number : Int64)
    (read : i64Cbor.readNumber? value = some number) : i64Cbor.number number = value := by
  cases value <;> simp only [i64Cbor] at read ⊢
  · rw [int64_read_toInt _ _ read]
  · rw [int64_read_toInt _ _ read]
  all_goals contradiction

theorem drisl_render_of_parse (profile : CidProfile) {bytes : List UInt8} {tree : Ordered (Cid profile)}
    (read : parseCbor? drislCbor (Cid.codec profile) bytes = some tree) :
    renderCbor? drislCbor (Cid.codec profile) tree = some bytes :=
  render_of_parse _ _ (leaf_reencode _ _ drisl_number_reencode (cid_reencode profile)) _ _ read

theorem atproto_render_of_parse_with_codec {Link : Type} (cid : CidCodec Link)
    (reencodes : ∀ bytes link, cid.parse? bytes = some link → cid.bytes link = bytes)
    {bytes : List UInt8} {tree : OrderedATProto Link}
    (read : parseCbor? i64Cbor cid bytes = some tree) : renderCbor? i64Cbor cid tree = some bytes :=
  render_of_parse _ _ (leaf_reencode _ _ atproto_number_reencode reencodes) _ _ read

theorem atproto_render_of_parse (profile : CidProfile) {bytes : List UInt8} {tree : OrderedATProto (Cid profile)}
    (read : parseCbor? i64Cbor (Cid.codec profile) bytes = some tree) :
    renderCbor? i64Cbor (Cid.codec profile) tree = some bytes :=
  atproto_render_of_parse_with_codec _ (cid_reencode profile) read

private theorem read_utf8Value (name : String) :
    String.fromUTF8? name.toByteArray.data.toList.toByteArray = some name := by
  have bytes : name.toByteArray.data.toList.toByteArray = name.toByteArray := by
    apply ByteArray.ext
    simp only [List.data_toByteArray]
  rw [bytes]
  unfold String.fromUTF8?
  rw [dite_eq_left name.isValidUTF8, Option.some.injEq]
  exact String.toByteArray_inj.mp rfl

section OrderedRoundtrip

variable {Numeric Link : Type} (numeric : CborCodec Numeric) (cid : CidCodec Link)

private def OrderedRead : {index : JsonIx} → RawSyn String (Scalar Numeric Link) index → Prop
  | .val, tree => readModel? numeric cid (emitModel numeric cid false tree) = some tree
  | .arr, tree => readItems? numeric cid (emitModel numeric cid false tree) = some tree
  | .obj, tree => readEntries? numeric cid (emitModel numeric cid false tree) = some tree

private theorem read_emit_ordered (ordinaryNumber : ∀ number, isLeaf (numeric.number number) ∧
      readCborLeaf? numeric cid (numeric.number number) = some (.data (.number number)))
    {index : JsonIx} (tree : RawSyn String (Scalar Numeric Link) index)
    (readCid : ∀ link ∈ links tree, cid.parse? (cid.bytes link) = some link) : OrderedRead numeric cid tree := by
  induction tree with
  | scalar leaf =>
    cases leaf with
    | link link =>
      have accepted := readCid link (by simp [links, RawSyn.scalars])
      simp [OrderedRead, emitModel, emitLeaf, readModel?, readCborLeaf?, accepted]
    | data data =>
      cases data with
      | bool flag => cases flag <;> rfl
      | null => rfl
      | bytes => rfl
      | string => simp [OrderedRead, emitModel, emitLeaf, utf8Value, readModel?, readCborLeaf?, read_utf8Value]
      | number value =>
        have ⟨nonContainer, parsed⟩ := ordinaryNumber value
        change readModel? numeric cid (numeric.number value) = _
        generalize numeric.number value = leafValue at nonContainer parsed ⊢
        cases leafValue <;> try exact nonContainer.elim
        all_goals simp [readModel?, parsed]
  | list _ ih | map _ ih =>
    have children := ih readCid
    simp_all [OrderedRead, emitModel, readModel?]
  | cons _ _ ih tail | objCons _ _ _ ih tail =>
    have first := ih fun link present => readCid link (by
      simp [links, RawSyn.scalars] at present ⊢
      exact Or.inl present)
    have rest := tail fun link present => readCid link (by
      simp [links, RawSyn.scalars] at present ⊢
      exact Or.inr present)
    simp_all [OrderedRead, emitModel, readItems?, readEntries?, utf8Value, read_utf8Value]
  | nil | objNil => rfl

private def OrderMatches : {index : JsonIx} → RawSyn String (Scalar Numeric Link) index → Prop
  | .val, tree => canonicalMaps (emitModel numeric cid false tree) = true →
      emitModel numeric cid true tree = emitModel numeric cid false tree
  | .arr, tree => canonicalItems (emitModel numeric cid false tree) = true →
      emitModel numeric cid true tree = emitModel numeric cid false tree
  | .obj, tree => canonicalEntries (emitModel numeric cid false tree) = true →
      emitModel numeric cid true tree = emitModel numeric cid false tree

private theorem emit_same_of_order {index : JsonIx} (tree : RawSyn String (Scalar Numeric Link) index) :
    OrderMatches numeric cid tree := by
  induction tree with
  | scalar | nil | objNil => intro; rfl
  | list items ih =>
    intro order
    simpa [emitModel] using congrArg Value.array (ih order)
  | map entries ih =>
    intro order
    obtain ⟨keys, children⟩ := Bool.and_eq_true_iff.mp order
    have sorted : strictlySorted ((emitModel numeric cid false entries).map fun entry => entry.1.encode) = true := keys
    simp [emitModel, ih children, sort_eq_of_sorted _ sorted]
  | cons _ _ ih tail | objCons _ _ _ ih tail =>
    intro order
    obtain ⟨head, rest⟩ := Bool.and_eq_true_iff.mp order
    simp [emitModel, ih head, tail rest]

private theorem ordered_roundtrip
    (ordinaryNumber : ∀ number, isLeaf (numeric.number number) ∧
      readCborLeaf? numeric cid (numeric.number number) = some (.data (.number number)))
    (tree : RawJson (Scalar Numeric Link))
    (readCid : ∀ link ∈ links tree, cid.parse? (cid.bytes link) = some link)
    (encodable : (emitModel numeric cid false tree).Encodable)
    (order : canonicalMaps (emitModel numeric cid false tree) = true) :
    renderCbor? numeric cid tree = some (emitModel numeric cid false tree).encode ∧
      parseCbor? numeric cid (emitModel numeric cid false tree).encode = some tree := by
  have parsed : parseCbor? numeric cid (emitModel numeric cid false tree).encode = some tree := by
    unfold parseCbor?
    rw [decode_encode _ encodable]
    change (if _ then interpretCbor? numeric cid _ else none) = _
    simp [order, interpret_of_sorted numeric cid _ order]
    exact read_emit_ordered numeric cid ordinaryNumber tree readCid
  exact ⟨by simp [renderCbor?, emit_same_of_order numeric cid tree order, parsed], parsed⟩

end OrderedRoundtrip

private theorem drisl_number_left {Link : Type} (cid : CidCodec Link) (number : Number) :
    isLeaf (drislCbor.number number) ∧
    readCborLeaf? drislCbor cid (drislCbor.number number) = some (.data (.number number)) := by
  cases number with
  | integer integer =>
    cases integer <;> rename_i amount <;>
      have bounded : amount.toNat < 18446744073709551616 := amount.toNat_lt
    all_goals simp [isLeaf, drislCbor, Integer.toCbor, readCborLeaf?, Integer.ofInt?, bounded]
  | float bits => simp [isLeaf, drislCbor, readCborLeaf?, bits.property]

private theorem atproto_number_left {Link : Type} (cid : CidCodec Link) (number : Int64) :
    isLeaf (i64Cbor.number number) ∧
    readCborLeaf? i64Cbor cid (i64Cbor.number number) = some (.data (.number number)) := by
  have read := int64_toInt number
  cases kind : number.toInt <;> simp_all only [i64Cbor, isLeaf, readCborLeaf?, true_and] <;> rfl

theorem drisl_ordered_roundtrip (profile : CidProfile) (tree : Ordered (Cid profile))
    (encodable : (emitModel drislCbor (Cid.codec profile) false tree).Encodable)
    (order : canonicalMaps (emitModel drislCbor (Cid.codec profile) false tree) = true) :
    let bytes := (emitModel drislCbor (Cid.codec profile) false tree).encode
    renderCbor? drislCbor (Cid.codec profile) tree = some bytes ∧
      parseCbor? drislCbor (Cid.codec profile) bytes = some tree :=
  ordered_roundtrip _ _ (drisl_number_left _) tree (fun link _ => Cid.parse_bytes profile link) encodable order

theorem atproto_ordered_roundtrip_with_codec {Link : Type} (cid : CidCodec Link) (tree : OrderedATProto Link)
    (readCid : ∀ link ∈ links tree, cid.parse? (cid.bytes link) = some link)
    (encodable : (emitModel i64Cbor cid false tree).Encodable)
    (order : canonicalMaps (emitModel i64Cbor cid false tree) = true) :
    let bytes := (emitModel i64Cbor cid false tree).encode
    renderCbor? i64Cbor cid tree = some bytes ∧ parseCbor? i64Cbor cid bytes = some tree :=
  ordered_roundtrip _ _ (atproto_number_left _) tree readCid encodable order

theorem atproto_ordered_roundtrip (profile : CidProfile) (tree : OrderedATProto (Cid profile))
    (encodable : (emitModel i64Cbor (Cid.codec profile) false tree).Encodable)
    (order : canonicalMaps (emitModel i64Cbor (Cid.codec profile) false tree) = true) :
    let bytes := (emitModel i64Cbor (Cid.codec profile) false tree).encode
    renderCbor? i64Cbor (Cid.codec profile) tree = some bytes ∧
      parseCbor? i64Cbor (Cid.codec profile) bytes = some tree :=
  atproto_ordered_roundtrip_with_codec _ tree (fun link _ => Cid.parse_bytes profile link) encodable order

private def unsortedTree : Ordered (Cid .dasl) :=
  .map (.objCons "b" (.scalar (.data .null)) (.objCons "a" (.scalar (.data .null)) .objNil))

private def sortedTree : Ordered (Cid .dasl) :=
  .map (.objCons "a" (.scalar (.data .null)) (.objCons "b" (.scalar (.data .null)) .objNil))

example : (renderCbor? drislCbor (Cid.codec .dasl) unsortedTree).bind
    (parseCbor? drislCbor (Cid.codec .dasl)) = some sortedTree := by
  have same : emitModel drislCbor (Cid.codec .dasl) true unsortedTree =
      emitModel drislCbor (Cid.codec .dasl) true sortedTree := by
    simp only [unsortedTree, sortedTree, emitModel, ite_true, List.mergeSort_pair]
    rfl
  obtain ⟨rendered, read⟩ := drisl_ordered_roundtrip .dasl sortedTree
    (by
      simp [emitModel, sortedTree, Value.Encodable, MapEncodable, emitLeaf, utf8Value, Value.null]
      decide +kernel)
    (by decide +kernel)
  have renderedSame : renderCbor? drislCbor (Cid.codec .dasl) unsortedTree =
      renderCbor? drislCbor (Cid.codec .dasl) sortedTree := by simp [renderCbor?, same]
  rw [renderedSame, rendered]
  exact read

end Silmaril.Proofs.Formats.Cbor.Drisl.Model
