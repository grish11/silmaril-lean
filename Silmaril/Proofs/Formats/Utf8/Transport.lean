module

public import Silmaril.Formats.Utf8.Defs
import Silmaril.Proofs.Formats.Utf8.Basic
import Silmaril.Proofs.Formats.Utf8.Core
import Silmaril.Proofs.Formats.Utf8.Encode

/-! # Proofs: byte regular expressions on encodings, as character conditions
(`Silmaril.Formats.Utf8.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Utf8.Transport

open Silmaril.Formats.Utf8 RegularExpression
open Silmaril.Proofs.Formats.Utf8.Encode

/-! ## `Good` expressions -/

theorem good_mul {r s : RegularExpression UInt8} (hr : Good r) (hs : Good s) : Good (r * s) := by
  intro w hw
  rw [← comp_def, matches', Language.mem_mul] at hw
  obtain ⟨a, ha, b, hb, rfl⟩ := hw
  exact Silmaril.Proofs.Formats.Utf8.isWellFormed_append (hr a ha) (hs b hb)

theorem good_add {r s : RegularExpression UInt8} (hr : Good r) (hs : Good s) : Good (r + s) := by
  intro w hw
  rw [← plus_def, matches', Language.mem_add] at hw
  rcases hw with hw | hw
  exacts [hr w hw, hs w hw]

theorem good_one : Good 1 := by
  intro w hw
  rw [← one_def, matches', Language.mem_one] at hw
  exact hw ▸ Silmaril.Proofs.Formats.Utf8.isWellFormed_nil

theorem good_star {r : RegularExpression UInt8} (hr : Good r) : Good (star r) := by
  intro w hw
  rw [matches', Language.mem_kstar] at hw
  obtain ⟨L, rfl, hL⟩ := hw
  induction L with
  | nil => exact Silmaril.Proofs.Formats.Utf8.isWellFormed_nil
  | cons y L ih =>
    rw [List.flatten_cons]
    exact Silmaril.Proofs.Formats.Utf8.isWellFormed_append (hr y (hL y (by simp)))
      (ih fun z hz => hL z (by simp [hz]))

theorem good_anyOf {l : List UInt8} (h : ∀ b ∈ l, b < 0x80) : Good (anyOf l) := by
  intro w hw
  obtain ⟨b, hb, rfl⟩ := Silmaril.Proofs.Formats.Utf8.mem_anyOf.mp hw
  exact Silmaril.Proofs.Formats.Utf8.isWellFormed_of_ascii (by simpa using h b hb)

theorem good_char {b : UInt8} (h : b < 0x80) : Good (char b) := by
  intro w hw
  rw [Silmaril.Proofs.Formats.Utf8.Core.mem_char.mp hw]
  exact Silmaril.Proofs.Formats.Utf8.isWellFormed_of_ascii (by simpa using h)

theorem uint8_lt_of_le_of_lt {a b c : UInt8} (h₁ : a ≤ b) (h₂ : b < c) : a < c :=
  UInt8.lt_iff_toNat_lt.mpr (Nat.lt_of_le_of_lt (UInt8.le_iff_toNat_le.mp h₁) (UInt8.lt_iff_toNat_lt.mp h₂))

theorem good_byteRange {lo hi : UInt8} (h : hi < 0x80) : Good (byteRange lo hi) := by
  intro w hw
  obtain ⟨b, rfl, -, hb⟩ := Silmaril.Proofs.Formats.Utf8.mem_byteRange.mp hw
  exact Silmaril.Proofs.Formats.Utf8.isWellFormed_of_ascii (by simpa using uint8_lt_of_le_of_lt hb h)

theorem good_word {l : List UInt8} (h : ∀ b ∈ l, b < 0x80) : Good (word l) := by
  intro w hw
  rw [Silmaril.Proofs.Formats.Utf8.mem_word.mp hw]
  exact Silmaril.Proofs.Formats.Utf8.isWellFormed_of_ascii h

theorem good_scalar : Good scalar := fun _ hw => Silmaril.Proofs.Formats.Utf8.scalar_isWellFormed hw

theorem good_multibyte : Good multibyte := fun w hw =>
  good_scalar w ((Language.mem_add _ _ _).mpr (Or.inr hw))

/-! ## Encodings of characters in expressions -/

theorem encode_mem_mul {r s : RegularExpression UInt8} (hr : Good r) (hs : Good s) {cs : List Char} :
    encode cs ∈ (r * s).matches' ↔
      ∃ c₁ c₂, cs = c₁ ++ c₂ ∧ encode c₁ ∈ r.matches' ∧ encode c₂ ∈ s.matches' := by
  rw [← comp_def, matches', Language.mem_mul]
  constructor
  · rintro ⟨a, ha, b, hb, h⟩
    obtain ⟨c₁, c₂, rfl, rfl, rfl⟩ := encode_eq_append h.symm (hr a ha) (hs b hb)
    exact ⟨c₁, c₂, rfl, ha, hb⟩
  · rintro ⟨c₁, c₂, rfl, h₁, h₂⟩
    exact ⟨_, h₁, _, h₂, (encode_append c₁ c₂).symm⟩

theorem encode_mem_add {r s : RegularExpression UInt8} {cs : List Char} :
    encode cs ∈ (r + s).matches' ↔ encode cs ∈ r.matches' ∨ encode cs ∈ s.matches' := by
  rw [← plus_def, matches', Language.mem_add]

theorem encode_mem_one {cs : List Char} : encode cs ∈ (1 : RegularExpression UInt8).matches' ↔ cs = [] := by
  rw [← one_def, matches', Language.mem_one]
  constructor
  · intro h; exact encode_injective (by rw [h]; rfl)
  · rintro rfl; rfl

theorem encode_mem_star {r : RegularExpression UInt8} (hr : Good r) {cs : List Char} :
    encode cs ∈ (star r).matches' ↔
      ∃ L : List (List Char), cs = L.flatten ∧ ∀ x ∈ L, encode x ∈ r.matches' := by
  rw [matches', Language.mem_kstar]
  constructor
  · rintro ⟨L, hL, hm⟩
    induction L generalizing cs with
    | nil => exact ⟨[], encode_injective (by rw [hL]; rfl), by simp⟩
    | cons y L ih =>
      rw [List.flatten_cons] at hL
      have hy := hm y (by simp)
      have hrest : IsWellFormed L.flatten := good_star hr _ ((Language.mem_kstar).mpr
        ⟨L, rfl, fun z hz => hm z (by simp [hz])⟩)
      obtain ⟨c₁, c₂, rfl, h₁, h₂⟩ := encode_eq_append hL (hr y hy) hrest
      obtain ⟨L', rfl, hL'⟩ := ih h₂ (fun z hz => hm z (by simp [hz]))
      refine ⟨c₁ :: L', by simp, ?_⟩
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · rw [h₁]; exact hy
      · exact hL' x hx
  · rintro ⟨L, rfl, hL⟩
    refine ⟨L.map encode, ?_, by simpa using hL⟩
    induction L with
    | nil => rfl
    | cons y L ih => simp [encode_append, ih fun z hz => hL z (by simp [hz])]

theorem encode_singleton_ascii {c : Char} (h : c.toNat < 0x80) :
    encode [c] = [UInt8.ofNat c.toNat] := by
  have := utf8EncodeChar_ofNat h
  rw [Char.ofNat_toNat] at this
  simp [encode, this]

theorem encode_mem_byteRange {lo hi : UInt8} (h : hi < 0x80) {cs : List Char} :
    encode cs ∈ (byteRange lo hi).matches' ↔
      ∃ c, cs = [c] ∧ lo.toNat ≤ c.toNat ∧ c.toNat ≤ hi.toNat := by
  rw [Silmaril.Proofs.Formats.Utf8.mem_byteRange]
  have hhi : hi.toNat < 0x80 := by simpa [UInt8.lt_iff_toNat_lt] using h
  constructor
  · rintro ⟨b, hb, hlo, hb'⟩
    have hb80 : b < 0x80 := uint8_lt_of_le_of_lt hb' h
    have := eq_ofAscii hb (by simpa using hb80)
    refine ⟨Char.ofNat b.toNat, by simpa [ofAscii] using this, ?_⟩
    have hbn : b.toNat < 0x80 := by simpa [UInt8.lt_iff_toNat_lt] using hb80
    have : (Char.ofNat b.toNat).toNat = b.toNat := toNat_ofNat_ascii (by omega)
    rw [this]
    exact ⟨UInt8.le_iff_toNat_le.mp hlo, UInt8.le_iff_toNat_le.mp hb'⟩
  · rintro ⟨c, rfl, h₁, h₂⟩
    refine ⟨UInt8.ofNat c.toNat, encode_singleton_ascii (by omega), ?_, ?_⟩ <;>
      simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat', Nat.reducePow] <;> omega

theorem encode_mem_char {b : UInt8} (h : b < 0x80) {cs : List Char} :
    encode cs ∈ (char b).matches' ↔ cs = [Char.ofNat b.toNat] := by
  rw [Silmaril.Proofs.Formats.Utf8.Core.mem_char]
  constructor
  · intro hb; simpa [ofAscii] using eq_ofAscii hb (by simpa using h)
  · rintro rfl; simpa [ofAscii] using encode_ofAscii (bs := [b]) (by simpa using h)

theorem mem_mul_length {r s : RegularExpression UInt8} {w : List UInt8} (h : w ∈ (r * s).matches')
    {m n : Nat} (hr : ∀ a ∈ r.matches', m ≤ a.length) (hs : ∀ b ∈ s.matches', n ≤ b.length) :
    m + n ≤ w.length := by
  rw [← comp_def, matches', Language.mem_mul] at h
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  have := hr a ha; have := hs b hb
  simp; omega

theorem byteRange_length {lo hi : UInt8} : ∀ a ∈ (byteRange lo hi).matches', 1 ≤ a.length := by
  intro a ha
  obtain ⟨b, rfl, -⟩ := Silmaril.Proofs.Formats.Utf8.mem_byteRange.mp ha
  simp

theorem char_length {x : UInt8} : ∀ a ∈ (char x).matches', 1 ≤ a.length := by
  intro a ha
  rw [Silmaril.Proofs.Formats.Utf8.Core.mem_char.mp ha]
  simp

theorem mul_length1 {r s : RegularExpression UInt8}
    (hr : ∀ a ∈ r.matches', 1 ≤ a.length) (hs : ∀ b ∈ s.matches', 1 ≤ b.length) :
    ∀ w ∈ (r * s).matches', 1 ≤ w.length := fun _ h => by
  have := mem_mul_length h hr hs; omega

theorem multibyte_length {w : List UInt8} (h : w ∈ multibyte.matches') : 2 ≤ w.length := by
  simp only [multibyte, seq2, seq3, seq4, tail, matches'_add, Language.mem_add] at h
  rcases h with (h | (((h | h) | h) | h)) | ((h | h) | h)
  · exact mem_mul_length h byteRange_length byteRange_length
  · exact mem_mul_length h (mul_length1 char_length byteRange_length) byteRange_length
  · exact mem_mul_length h (mul_length1 byteRange_length byteRange_length) byteRange_length
  · exact mem_mul_length h (mul_length1 char_length byteRange_length) byteRange_length
  · exact mem_mul_length h (mul_length1 byteRange_length byteRange_length) byteRange_length
  · have := mem_mul_length h (mul_length1 (mul_length1 char_length byteRange_length)
      byteRange_length) byteRange_length; omega
  · have := mem_mul_length h (mul_length1 (mul_length1 byteRange_length byteRange_length)
      byteRange_length) byteRange_length; omega
  · have := mem_mul_length h (mul_length1 (mul_length1 char_length byteRange_length)
      byteRange_length) byteRange_length; omega

theorem utf8EncodeChar_length {c : Char} (h : 0x80 ≤ c.toNat) : 2 ≤ (String.utf8EncodeChar c).length := by
  simp only [Char.toNat] at h
  simp only [String.utf8EncodeChar]
  split_ifs with h1 h2 h3 <;> first | omega | simp

theorem encode_mem_multibyte {cs : List Char} :
    encode cs ∈ multibyte.matches' ↔ ∃ c, cs = [c] ∧ 0x80 ≤ c.toNat := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Silmaril.Proofs.Formats.Utf8.Core.exists_char_of_mem_scalar
      ((Language.mem_add _ _ _).mpr (Or.inr h))
    have hcs : cs = [c] := encode_injective (by rw [← hc]; simp [encode])
    subst hcs
    refine ⟨c, rfl, ?_⟩
    by_contra hlt
    have := multibyte_length h
    rw [encode_singleton_ascii (by omega)] at this
    simp at this
  · rintro ⟨c, rfl, hc⟩
    have hs := Silmaril.Proofs.Formats.Utf8.Core.utf8EncodeChar_mem_scalar c
    rw [scalar, matches'_add, Language.mem_add] at hs
    have he : encode [c] = String.utf8EncodeChar c := by simp [encode]
    rw [he]
    rcases hs with hs | hs
    · obtain ⟨b, hb, -⟩ := Silmaril.Proofs.Formats.Utf8.mem_byteRange.mp hs
      have := utf8EncodeChar_length hc
      rw [hb] at this; simp at this
    · exact hs

theorem encode_mem_anyOf {l : List UInt8} (h : ∀ b ∈ l, b < 0x80) {cs : List Char} :
    encode cs ∈ (anyOf l).matches' ↔ ∃ b ∈ l, cs = [Char.ofNat b.toNat] := by
  rw [Silmaril.Proofs.Formats.Utf8.mem_anyOf]
  constructor
  · rintro ⟨b, hb, he⟩
    exact ⟨b, hb, by simpa [ofAscii] using eq_ofAscii he (by simpa using h b hb)⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, by simpa [ofAscii] using encode_ofAscii (bs := [b]) (by simpa using h b hb)⟩

end Silmaril.Proofs.Formats.Utf8.Transport

end
