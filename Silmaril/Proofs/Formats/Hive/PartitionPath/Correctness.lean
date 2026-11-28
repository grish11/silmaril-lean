module

public import Silmaril.Formats.Hive.PartitionPath.Defs
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Hive.PartitionPath

open Silmaril.Formats.Hive.PartitionPath

namespace Percent

open Silmaril.Formats.Hive.PartitionPath.Percent

private theorem hexValue_hexDigit (n : Nat) (h : n < 16) :
    hexValue (hexDigit n) = some n := by
  unfold hexDigit
  have digit (x : Nat) (hx : x < 256) : (UInt8.ofNat x).toNat = x := by
    simpa [UInt8.toNat_ofNat] using Nat.mod_eq_of_lt hx
  split <;> rename_i hn
  · unfold hexValue
    rw [digit _ (by omega)]
    rw [ite_eq_left (by omega)]
    congr 1
    omega
  · unfold hexValue
    rw [digit _ (by omega)]
    rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    congr 1
    omega

private theorem unescapeRev_escapeWith (escapeUnderscore : Bool) (bytes acc : List UInt8) :
    unescapeRev (escapeWith escapeUnderscore bytes) acc = .ok (acc.reverse ++ bytes) := by
  induction bytes generalizing acc with
  | nil => simp [escapeWith, unescapeRev]
  | cons b rest ih =>
    change unescapeRev (escapeByteWith escapeUnderscore b ++ escapeWith escapeUnderscore rest) acc = _
    by_cases h : (unreserved b && !(escapeUnderscore && b == 95)) = true
    · have hb : (b == (37 : UInt8)) = false := by
        apply Bool.eq_false_iff.mpr
        intro he
        have he' : b = 37 := beq_iff_eq.mp he
        subst b
        simp [unreserved] at h
      simp only [escapeByteWith, h, ite_true, List.singleton_append]
      rw [unescapeRev.eq_def]
      simp [hb, ih, List.append_assoc]
    · have hi : b.toNat / 16 < 16 := by have := UInt8.toNat_lt b; omega
      have lo : b.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
      have hb : UInt8.ofNat (16 * (b.toNat / 16) + b.toNat % 16) = b := by
        have he : 16 * (b.toNat / 16) + b.toNat % 16 = b.toNat := by omega
        simp [he]
      simp only [escapeByteWith, h]
      simp [unescapeRev, hexValue_hexDigit _ hi, hexValue_hexDigit _ lo, hb, ih, List.append_assoc]

theorem unescape_escapeWith (escapeUnderscore : Bool) (bytes : List UInt8) :
    unescape (escapeWith escapeUnderscore bytes) = .ok bytes := by
  simpa [unescape] using unescapeRev_escapeWith escapeUnderscore bytes []

theorem unescape_escape (bytes : List UInt8) : unescape (escape bytes) = .ok bytes :=
  unescape_escapeWith false bytes

private theorem hexDigit_range (n : Nat) (h : n < 16) :
    let c := (hexDigit n).toNat
    (48 ≤ c ∧ c ≤ 57) ∨ (65 ≤ c ∧ c ≤ 70) := by
  unfold hexDigit
  split <;> simp only [UInt8.toNat_ofNat'] <;> omega

private theorem hexDigit_safe (n : Nat) (h : n < 16) :
    (hexDigit n).toNat < 128 ∧ hexDigit n ≠ 47 ∧ hexDigit n ≠ 61 ∧ hexDigit n ≠ 95 := by
  have range := hexDigit_range n h
  refine ⟨by omega, ?_, ?_, ?_⟩
  all_goals
    intro equal
    rw [equal] at range
    contradiction

theorem escapeWith_safe {escapeUnderscore : Bool} {bytes : List UInt8} {c : UInt8}
    (h : c ∈ escapeWith escapeUnderscore bytes) :
    c.toNat < 128 ∧ c ≠ 47 ∧ c ≠ 61 ∧ (escapeUnderscore = true → c ≠ 95) := by
  obtain ⟨b, _, hc⟩ := List.mem_flatMap.mp h
  by_cases hu : (unreserved b && !(escapeUnderscore && b == 95)) = true
  · simp only [escapeByteWith, hu, ite_true, List.mem_singleton] at hc
    subst c
    simp only [Bool.and_eq_true] at hu
    obtain ⟨reserved, underscore⟩ := hu
    simp only [unreserved, decide_eq_true_eq] at reserved
    refine ⟨by omega, ?_, ?_, ?_⟩
    · intro equal
      subst b
      contradiction
    · intro equal
      subst b
      contradiction
    · rintro rfl rfl
      simp at underscore
  · have hu' := Bool.eq_false_iff.mpr hu
    simp only [escapeByteWith, hu', Bool.false_eq_true, ite_false, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨by decide, by decide, by decide, fun _ => by decide⟩
    · obtain ⟨ascii, slash, equals, underscore⟩ :=
        hexDigit_safe (b.toNat / 16) (by have := UInt8.toNat_lt b; omega)
      exact ⟨ascii, slash, equals, fun _ => underscore⟩
    · obtain ⟨ascii, slash, equals, underscore⟩ :=
        hexDigit_safe (b.toNat % 16) (Nat.mod_lt _ (by decide))
      exact ⟨ascii, slash, equals, fun _ => underscore⟩

theorem escape_safe {bytes : List UInt8} {c : UInt8} (h : c ∈ escape bytes) :
    c.toNat < 128 ∧ c ≠ 47 ∧ c ≠ 61 :=
  let safe := escapeWith_safe (escapeUnderscore := false) h
  ⟨safe.1, safe.2.1, safe.2.2.1⟩

private theorem utf8Encode_ascii (bytes : List UInt8) (h : ∀ b ∈ bytes, b.toNat < 128) :
    ((bytes.map fun b => Char.ofNat b.toNat).utf8Encode).data.toList = bytes := by
  induction bytes with
  | nil => rfl
  | cons b rest ih =>
    have hb := h b (by simp)
    have hChar : b.toNat.isValidChar := Or.inl (by omega)
    have hv : (Char.ofNat b.toNat).val = UInt32.ofNat b.toNat := by
      rw [Char.ofNat, dite_eq_left hChar]
      apply UInt32.toNat.inj
      simp [Char.ofNatAux]
    have hs : (Char.ofNat b.toNat).utf8Size = 1 := by
      simp [Char.utf8Size, hv, UInt32.le_iff_toNat_le, UInt32.toNat_ofNat]
      omega
    rw [List.map_cons, List.utf8Encode_cons, List.utf8Encode_singleton,
      ByteArray.toList_data_append, String.utf8EncodeChar_eq_singleton hs,
      ih (fun c hc => h c (List.mem_cons_of_mem _ hc))]
    simp only [hv, UInt32.toUInt8_ofNat', UInt8.ofNat_toNat]
    rfl

theorem decode_encodeWith (escapeUnderscore : Bool) (value : String) : decode (encodeWith escapeUnderscore value) = .ok value := by
  have h : (encodeWith escapeUnderscore value).toUTF8.data.toList = escapeWith escapeUnderscore value.toUTF8.data.toList := by
    simp only [encodeWith, String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
    exact utf8Encode_ascii _ (fun _ h => (escapeWith_safe h).1)
  unfold decode
  rw [h, unescape_escapeWith]
  have hv := value.isValidUTF8
  change (match String.fromUTF8? value.toByteArray with
    | some text => Except.ok text
    | none => Except.error Error.invalidUtf8) = Except.ok value
  simp [String.fromUTF8?, hv]

theorem decode_encode (value : String) : decode (encode value) = .ok value :=
  decode_encodeWith false value

theorem encodeWith_avoids_underscore (value : String) : '_' ∉ (encodeWith true value).toList := by
  simp only [encodeWith, String.toList_ofList, List.mem_map]
  rintro ⟨byte, hit, equal⟩
  obtain ⟨ascii, _, _, noUnderscore⟩ := escapeWith_safe hit
  have valid : byte.toNat.isValidChar := Or.inl (by omega)
  have code : (Char.ofNat byte.toNat).toNat = byte.toNat := by
    simp [Char.toNat, Char.ofNat, valid, Char.ofNatAux]
  have isUnderscore : byte.toNat = 95 := by
    rw [← code, equal]
    rfl
  exact noUnderscore rfl (UInt8.toNat.inj isUnderscore)

end Percent

theorem validateKeys_nodup {keys : List String} (h : validateKeys keys = .ok ()) :
    keys.Nodup := by
  induction keys with
  | nil => simp
  | cons key tail ih =>
    unfold validateKeys at h
    split at h
    · contradiction
    split at h
    · contradiction
    rename_i hn
    exact List.nodup_cons.mpr ⟨by simpa [List.contains_iff_mem] using hn, ih h⟩

theorem lookup_eq_some_iff {entries : Partition} {key : String} {value : Option String}
    (h : (entries.map Prod.fst).Nodup) : lookup key entries = some value ↔ (key, value) ∈ entries := by
  induction entries with
  | nil => simp [lookup]
  | cons entry tail ih =>
    obtain ⟨name, text⟩ := entry
    have hn := List.nodup_cons.mp h
    by_cases hk : name = key
    · subst name
      have hm : (key, value) ∉ tail := fun hmem => hn.1 (List.mem_map.mpr ⟨(key, value), hmem, rfl⟩)
      simp [lookup, hm, eq_comm]
    · simpa [lookup, hk, Ne.symm hk] using ih hn.2

theorem validate_lookup {options : Options} {entries : Partition}
    (h : validate options entries = .ok ()) :
    (entries.map Prod.fst).Nodup ∧
      ∀ key ∈ options.requiredKeys, ∃ value, lookup key entries = some value := by
  cases hv : validateKeys (entries.map Prod.fst) with
  | error _ => simp [validate, hv, bind, Except.bind] at h
  | ok _ =>
    have hn := validateKeys_nodup hv
    refine ⟨hn, ?_⟩
    cases hm : options.requiredKeys.find? (fun key => !(entries.map Prod.fst).contains key) with
    | some _ =>
      simp only [validate, hv, hm, bind, Except.bind] at h
      cases h
    | none =>
      have hm' := List.find?_eq_none.mp hm
      intro key hk
      have hp : key ∈ entries.map Prod.fst := by
        simpa [List.contains_iff_mem] using hm' key hk
      obtain ⟨⟨name, value⟩, he, rfl⟩ := List.mem_map.mp hp
      exact ⟨value, (lookup_eq_some_iff hn).mpr he⟩

theorem parse_lookup {options : Options} {path : String} {entries : Partition}
    (h : parse options path = .ok entries) :
    (entries.map Prod.fst).Nodup ∧
      ∀ key ∈ options.requiredKeys, ∃ value, lookup key entries = some value := by
  unfold parse at h
  split at h
  · contradiction
  · generalize (if path.isEmpty then Except.ok [] else
      (path.splitOn "/").mapM (parseSegment options)) = checked at h
    cases checked with
    | error _ => cases h
    | ok checked =>
      cases validation : validate options checked with
      | error err => simp [bind, Except.bind, validation] at h
      | ok checkedUnit =>
        have he : checked = entries := by simpa [bind, Except.bind, validation, pure, Except.pure] using h
        subst entries
        cases checkedUnit
        exact validate_lookup validation

end Silmaril.Proofs.Formats.Hive.PartitionPath
