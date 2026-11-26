module

public import Silmaril.Formats.ThriftCompact.Defs
import Init.Data.ByteArray.Lemmas
import Init.Omega

namespace Silmaril.Proofs.Formats.ThriftCompact

open Silmaril.Formats Silmaril.Formats.ThriftCompact

private theorem getOctet_eq (source : Bytes) (offset : Nat) :
    source.data[offset]? = source.toList[offset]? := by
  rw [Bytes.toList, Array.getElem?_toList]
  rfl

private theorem go_sound {mode : VarintMode} {source : Bytes} {fuel offset value next : Nat}
    (h : readVarint.go mode source fuel offset = .ok (value, next)) :
    ∃ octets suffix : List UInt8,
      source.toList.drop offset = octets ++ suffix ∧
      VarintWire mode octets value ∧ octets.length ≤ fuel ∧ next = offset + octets.length := by
  induction fuel generalizing offset value next with
  | zero => simp [readVarint.go] at h
  | succ fuel ih =>
    rw [readVarint.go, getOctet_eq] at h
    cases hb : source.toList[offset]? with
    | none => simp [hb] at h
    | some byte =>
      have hlt : offset < source.toList.length := by
        apply Classical.byContradiction
        intro hge
        simp [List.getElem?_eq_none (by omega : source.toList.length ≤ offset)] at hb
      have hdrop : source.toList.drop offset = byte :: source.toList.drop (offset + 1) := by
        have eq : source.toList[offset] = byte := by simpa only [getElem?_def, dite_eq_left hlt, Option.some.injEq] using hb
        simp only [List.drop_eq_getElem_cons hlt, eq]
      by_cases terminal : byte.toNat < 128
      · simp [hb, terminal] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨[byte], _, hdrop, .last byte terminal, by simp, rfl⟩
      · cases hr : readVarint.go mode source fuel (offset + 1) with
        | error err => simp [hb, terminal, hr] at h
        | ok result =>
          obtain ⟨high, endOffset⟩ := result
          by_cases redundant : mode = .canonical ∧ high = 0
          · simp only [hb, ite_eq_right terminal, hr, ite_eq_left redundant, reduceCtorEq] at h
          · simp [hb, terminal, hr, redundant] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨octets, suffix, hs, wire, hlen, hend⟩ := ih hr
            refine ⟨byte :: octets, suffix, ?_, .more byte (by omega) wire (fun hm hz => redundant ⟨hm, hz⟩), ?_, ?_⟩
            · rw [hdrop, hs]; rfl
            · simp; omega
            · simp; omega

private theorem head_of_drop {source : Bytes} {offset : Nat} {byte : UInt8}
    {tail : List UInt8} (h : source.toList.drop offset = byte :: tail) :
    source.data[offset]? = some byte ∧ source.toList.drop (offset + 1) = tail := by
  have hlt : offset < source.toList.length := by
    apply Classical.byContradiction
    intro hge
    simp [List.drop_of_length_le (by omega : source.toList.length ≤ offset)] at h
  rw [List.drop_eq_getElem_cons hlt] at h
  obtain ⟨rfl, rfl⟩ := List.cons.inj h
  exact ⟨by rw [getOctet_eq, getElem?_def, dite_eq_left hlt], rfl⟩

private theorem go_complete {mode : VarintMode} {octets : List UInt8} {value : Nat}
    (wire : VarintWire mode octets value)
    {source : Bytes} {fuel offset : Nat} {suffix : List UInt8}
    (hsource : source.toList.drop offset = octets ++ suffix) (hlen : octets.length ≤ fuel) :
    readVarint.go mode source fuel offset = .ok (value, offset + octets.length) := by
  induction wire generalizing fuel offset with
  | last byte terminal =>
    cases fuel with
    | zero => simp at hlen
    | succ fuel =>
      have hb := (head_of_drop hsource).1
      simp [readVarint.go, hb, terminal]
  | more byte continued wire minimal ih =>
    cases fuel with
    | zero => simp at hlen
    | succ fuel =>
      obtain ⟨hb, ht⟩ := head_of_drop hsource
      have hr := ih ht (by simpa using hlen)
      have terminal : ¬byte.toNat < 128 := by omega
      have redundant : ¬(mode = .canonical ∧ _ = 0) := fun h => minimal h.1 h.2
      simp [readVarint.go, hb, terminal, hr, redundant]
      omega

public theorem readVarint_ok_iff {width : Width} {mode : VarintMode}
    {source : Bytes} {offset value next : Nat} :
    readVarint width mode source offset = .ok (value, next) ↔
      value < 2 ^ width.bits ∧
      ∃ octets suffix : List UInt8,
        source.toList.drop offset = octets ++ suffix ∧
        VarintWire mode octets value ∧ octets.length ≤ width.byteCount ∧
        next = offset + octets.length := by
  constructor
  · intro h
    cases hr : readVarint.go mode source width.byteCount offset with
    | error err => simp [readVarint, hr] at h
    | ok result =>
      obtain ⟨code, endOffset⟩ := result
      by_cases bounded : code < 2 ^ width.bits
      · simp [readVarint, hr, bounded] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨bounded, go_sound hr⟩
      · simp [readVarint, hr, bounded] at h
  · rintro ⟨bounded, octets, suffix, hsource, wire, hlen, rfl⟩
    simp [readVarint, go_complete wire hsource hlen, bounded]

public theorem unzigzag_zigzag (value : Int) : unzigzag (zigzag value) = value := by
  unfold zigzag unzigzag
  split <;> split <;> omega

public theorem zigzag_unzigzag (value : Nat) : zigzag (unzigzag value) = value := by
  unfold unzigzag zigzag
  split <;> split <;> omega

public theorem zigzag_lt_iff (width : Width) (value : Int) :
    zigzag value < 2 ^ width.bits ↔ -width.halfRange ≤ value ∧ value < width.halfRange := by
  cases width <;> simp only [Width.bits, Width.halfRange, zigzag, Nat.reduceSub, Nat.reducePow,
    Int.reducePow] <;> split <;> omega

public theorem readSigned_ok_iff {width : Width} {mode : VarintMode}
    {source : Bytes} {offset next : Nat} {value : Int} :
    readSigned width mode source offset = .ok (value, next) ↔
      (-width.halfRange ≤ value ∧ value < width.halfRange) ∧
      ∃ octets suffix : List UInt8,
        source.toList.drop offset = octets ++ suffix ∧
        VarintWire mode octets (zigzag value) ∧ octets.length ≤ width.byteCount ∧
        next = offset + octets.length := by
  constructor
  · intro h
    cases hr : readVarint width mode source offset with
    | error err => simp [readSigned, hr, bind, Except.bind] at h
    | ok result =>
      obtain ⟨code, consumed⟩ := result
      simp [readSigned, hr, bind, Except.bind, pure, Except.pure] at h
      obtain ⟨rfl, rfl⟩ := h
      simpa only [zigzag_unzigzag, ← zigzag_lt_iff] using readVarint_ok_iff.mp hr
  · rintro ⟨bounded, h⟩
    have hread := readVarint_ok_iff.mpr ⟨(zigzag_lt_iff width value).mpr bounded, h⟩
    simp [readSigned, hread, unzigzag_zigzag, bind, Except.bind, pure, Except.pure]

private theorem varintBytes_wire (mode : VarintMode) {fuel value : Nat}
    (h : value < 128 ^ fuel) (positive : 0 < fuel) :
    VarintWire mode (varintBytes value) value ∧ (varintBytes value).length ≤ fuel := by
  induction fuel generalizing value with
  | zero => omega
  | succ fuel ih =>
    rw [varintBytes]
    by_cases terminal : value < 128
    · have hb : (UInt8.ofNat value).toNat = value := by
        change _ % 256 = _
        exact Nat.mod_eq_of_lt (by omega)
      have wire := VarintWire.last (mode := mode) (UInt8.ofNat value) (by omega)
      rw [hb] at wire
      exact ⟨by simpa only [ite_eq_left terminal], by simp [terminal]⟩
    · have hhigh : value / 128 < 128 ^ fuel :=
        (Nat.div_lt_iff_lt_mul (by decide)).mpr (by simpa [Nat.pow_succ] using h)
      have fuelPositive : 0 < fuel := by
        cases fuel with
        | zero => simp at hhigh; omega
        | succ _ => omega
      obtain ⟨wire, hlen⟩ := ih hhigh fuelPositive
      have hb : (UInt8.ofNat (128 + value % 128)).toNat = 128 + value % 128 := by
        change _ % 256 = _
        exact Nat.mod_eq_of_lt (by omega)
      have encoded := VarintWire.more (UInt8.ofNat (128 + value % 128)) (by omega)
        wire (show mode = .canonical → value / 128 ≠ 0 by omega)
      rw [hb, show 128 + value % 128 - 128 + 128 * (value / 128) = value by omega] at encoded
      exact ⟨by simpa only [ite_eq_right terminal], by simpa [terminal] using hlen⟩

public theorem encodeSigned?_isSome_iff (width : Width) (value : Int) :
    (encodeSigned? width value).isSome = true ↔
      -width.halfRange ≤ value ∧ value < width.halfRange := by
  rw [← zigzag_lt_iff]
  by_cases bounded : zigzag value < 2 ^ width.bits <;> simp [encodeSigned?, bounded]

public theorem readSigned_encodeSigned? {width : Width} {value : Int} {encoded : Bytes}
    (hencode : encodeSigned? width value = some encoded) (mode : VarintMode)
    (leading trailing : Bytes) :
    readSigned width mode (leading.append (encoded.append trailing)) leading.length =
      .ok (value, leading.length + encoded.length) := by
  by_cases bounded : zigzag value < 2 ^ width.bits
  · simp [encodeSigned?, bounded] at hencode
    subst encoded
    have capacity : 2 ^ width.bits ≤ 128 ^ width.byteCount := by cases width <;> decide
    have positive : 0 < width.byteCount := by cases width <;> decide
    obtain ⟨wire, hlen⟩ := varintBytes_wire mode (Nat.lt_of_lt_of_le bounded capacity) positive
    apply readSigned_ok_iff.mpr
    refine ⟨(zigzag_lt_iff width value).mp bounded, _, trailing.toList, ?_, wire, hlen, ?_⟩
    · simp only [Bytes.toList_append, Bytes.toList_ofList, ← Bytes.length_toList leading,
        List.drop_left]
    · simp
  · simp [encodeSigned?, bounded] at hencode

end Silmaril.Proofs.Formats.ThriftCompact
