module

public import Silmaril.Formats.Utf8.Defs
import Silmaril.Proofs.Formats.Utf8.Core

/-! # Proofs: the encoding of character lists (`Silmaril.Formats.Utf8.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Utf8.Encode

open Silmaril.Formats.Utf8

theorem encode_nil : encode [] = [] := rfl

theorem encode_cons (c : Char) (cs : List Char) :
    encode (c :: cs) = String.utf8EncodeChar c ++ encode cs := List.flatMap_cons

theorem encode_append (a b : List Char) : encode (a ++ b) = encode a ++ encode b :=
  List.flatMap_append

theorem utf8Encode_data (cs : List Char) : cs.utf8Encode.data.toList = encode cs :=
  List.toByteArray_inj.mp rfl

theorem encode_injective {cs cs' : List Char} (h : encode cs = encode cs') : cs = cs' := by
  have h1 : cs.utf8Encode = cs'.utf8Encode := by
    apply ByteArray.ext
    apply Array.ext'
    rw [utf8Encode_data, utf8Encode_data, h]
  have h2 : String.ofList cs = String.ofList cs' :=
    String.toByteArray_inj.mp (by rw [String.toByteArray_ofList, String.toByteArray_ofList, h1])
  rw [← String.toList_ofList (l := cs), ← String.toList_ofList (l := cs'), h2]

theorem isWellFormed_encode (cs : List Char) : IsWellFormed (encode cs) :=
  Silmaril.Proofs.Formats.Utf8.Core.isWellFormed_iff_exists_chars.mpr ⟨cs, rfl⟩

theorem encode_eq_append {cs : List Char} {a b : List UInt8} (h : encode cs = a ++ b)
    (ha : IsWellFormed a) (hb : IsWellFormed b) :
    ∃ c₁ c₂, cs = c₁ ++ c₂ ∧ encode c₁ = a ∧ encode c₂ = b := by
  obtain ⟨c₁, rfl⟩ := Silmaril.Proofs.Formats.Utf8.Core.isWellFormed_iff_exists_chars.mp ha
  obtain ⟨c₂, rfl⟩ := Silmaril.Proofs.Formats.Utf8.Core.isWellFormed_iff_exists_chars.mp hb
  exact ⟨c₁, c₂, encode_injective (by rw [h, encode_append]; rfl), rfl, rfl⟩

theorem fromUTF8?_eq_some {b : ByteArray} {s : String} (h : String.fromUTF8? b = some s) :
    b.data.toList = encode s.toList := by
  unfold String.fromUTF8? at h
  split at h
  · cases h
    rw [← utf8Encode_data, String.utf8Encode_toList]
    rfl
  · simp at h

theorem fromUTF8?_encode (cs : List Char) :
    ∃ s, String.fromUTF8? (encode cs).toByteArray = some s ∧ s.toList = cs := by
  have hv : (encode cs).toByteArray.IsValidUTF8 :=
    Silmaril.Proofs.Formats.Utf8.Core.isValidUTF8_iff.mpr
      (by rw [List.data_toByteArray]; exact isWellFormed_encode cs)
  refine ⟨String.fromUTF8 _ hv, by simp [String.fromUTF8?, hv], ?_⟩
  apply encode_injective
  have := fromUTF8?_eq_some (b := (encode cs).toByteArray) (s := String.fromUTF8 _ hv)
    (by simp [String.fromUTF8?, hv])
  rw [← this, List.data_toByteArray]

theorem toNat_ofNat_ascii {n : Nat} (h : n < 0x80) : (Char.ofNat n).toNat = n := by
  unfold Char.ofNat
  split
  · simp [Char.ofNatAux, UInt32.toNat_ofNatLT, Char.toNat]
  · rename_i h'; exact absurd (Or.inl (by omega)) h'

theorem utf8EncodeChar_ofNat {n : Nat} (h : n < 0x80) :
    String.utf8EncodeChar (Char.ofNat n) = [UInt8.ofNat n] := by
  have hv : (Char.ofNat n).val.toNat = n := toNat_ofNat_ascii h
  simp only [String.utf8EncodeChar, hv]
  split
  · rfl
  · omega

theorem encode_ofAscii {bs : List UInt8} (h : ∀ b ∈ bs, b < 0x80) : encode (ofAscii bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [ofAscii, List.map_cons]
    rw [encode_cons, utf8EncodeChar_ofNat (by have := h b (by simp); simpa [UInt8.lt_iff_toNat_lt] using this),
      UInt8.ofNat_toNat]
    exact congrArg (b :: ·) (ih fun x hx => h x (by simp [hx]))

theorem eq_ofAscii {cs : List Char} {bs : List UInt8} (h : encode cs = bs)
    (ha : ∀ b ∈ bs, b < 0x80) : cs = ofAscii bs :=
  encode_injective (by rw [h, encode_ofAscii ha])

end Silmaril.Proofs.Formats.Utf8.Encode

end
