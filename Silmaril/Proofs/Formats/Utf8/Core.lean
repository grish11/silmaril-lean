module

public import Silmaril.Formats.Utf8.Defs
import Silmaril.Proofs.Formats.Utf8.Basic

/-! # Proofs: well-formed UTF-8 is exactly Lean core's encoding (`Silmaril.Formats.Utf8.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Utf8.Core

open Silmaril.Formats.Utf8 RegularExpression

theorem mem_char {a : UInt8} {w : List UInt8} : w ∈ (char a).matches' ↔ w = [a] := Iff.rfl

theorem ofNat_mem_byteRange {n : Nat} {lo hi : UInt8} (h₁ : lo.toNat ≤ n) (h₂ : n ≤ hi.toNat) :
    [UInt8.ofNat n] ∈ (byteRange lo hi).matches' := by
  have := hi.toNat_lt
  refine mem_byteRange.mpr ⟨_, rfl, ?_, ?_⟩ <;>
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat', Nat.reducePow] <;> omega

theorem ofNat_mem_char {n : Nat} {a : UInt8} (h : n = a.toNat) :
    [UInt8.ofNat n] ∈ (char a).matches' := by
  subst h; rw [UInt8.ofNat_toNat]; rfl

theorem mem_add_left {P Q : RegularExpression UInt8} {w : List UInt8} (h : w ∈ P.matches') :
    w ∈ (P + Q).matches' := (Language.mem_add _ _ _).mpr (Or.inl h)

theorem mem_add_right {P Q : RegularExpression UInt8} {w : List UInt8} (h : w ∈ Q.matches') :
    w ∈ (P + Q).matches' := (Language.mem_add _ _ _).mpr (Or.inr h)

theorem mem_mul_of {P Q : RegularExpression UInt8} {a b : List UInt8}
    (ha : a ∈ P.matches') (hb : b ∈ Q.matches') : a ++ b ∈ (P * Q).matches' :=
  Language.append_mem_mul ha hb

/-- Close a `UInt8` literal bound goal over `Nat`. -/
local macro "bnd" : tactic => `(tactic| (simp only [UInt8.reduceToNat]; omega))

theorem utf8EncodeChar_mem_scalar (c : Char) : String.utf8EncodeChar c ∈ scalar.matches' := by
  have hv : c.val.toNat < 0xD800 ∨ (0xDFFF < c.val.toNat ∧ c.val.toNat < 0x110000) := c.valid
  unfold String.utf8EncodeChar scalar multibyte seq2 seq3 seq4 ascii tail
  generalize c.val.toNat = v at hv ⊢
  simp only
  split
  · exact mem_add_left (ofNat_mem_byteRange (by bnd) (by bnd))
  split
  · refine mem_add_right (mem_add_left (mem_add_left
      (mem_mul_of (a := [_]) (b := [_]) ?_ ?_))) <;>
      exact ofNat_mem_byteRange (by bnd) (by bnd)
  split
  · refine mem_add_right (mem_add_left (mem_add_right ?_))
    by_cases h1 : v < 0x1000
    · refine mem_add_left (mem_add_left (mem_add_left
        (mem_mul_of (a := [_, _]) (b := [_]) (mem_mul_of (a := [_]) (b := [_]) ?_ ?_) ?_)))
      · exact ofNat_mem_char (by bnd)
      all_goals exact ofNat_mem_byteRange (by bnd) (by bnd)
    by_cases h2 : v < 0xD000
    · refine mem_add_left (mem_add_left (mem_add_right
        (mem_mul_of (a := [_, _]) (b := [_]) (mem_mul_of (a := [_]) (b := [_]) ?_ ?_) ?_)))
      all_goals exact ofNat_mem_byteRange (by bnd) (by bnd)
    by_cases h3 : v < 0xD800
    · refine mem_add_left (mem_add_right
        (mem_mul_of (a := [_, _]) (b := [_]) (mem_mul_of (a := [_]) (b := [_]) ?_ ?_) ?_))
      · exact ofNat_mem_char (by bnd)
      all_goals exact ofNat_mem_byteRange (by bnd) (by bnd)
    · refine mem_add_right
        (mem_mul_of (a := [_, _]) (b := [_]) (mem_mul_of (a := [_]) (b := [_]) ?_ ?_) ?_)
      all_goals exact ofNat_mem_byteRange (by bnd) (by bnd)
  · refine mem_add_right (mem_add_right ?_)
    by_cases h1 : v < 0x40000
    · refine mem_add_left (mem_add_left
        (mem_mul_of (a := [_, _, _]) (b := [_]) (mem_mul_of (a := [_, _]) (b := [_])
          (mem_mul_of (a := [_]) (b := [_]) ?_ ?_) ?_) ?_))
      · exact ofNat_mem_char (by bnd)
      all_goals exact ofNat_mem_byteRange (by bnd) (by bnd)
    by_cases h2 : v < 0x100000
    · refine mem_add_left (mem_add_right
        (mem_mul_of (a := [_, _, _]) (b := [_]) (mem_mul_of (a := [_, _]) (b := [_])
          (mem_mul_of (a := [_]) (b := [_]) ?_ ?_) ?_) ?_))
      all_goals exact ofNat_mem_byteRange (by bnd) (by bnd)
    · refine mem_add_right
        (mem_mul_of (a := [_, _, _]) (b := [_]) (mem_mul_of (a := [_, _]) (b := [_])
          (mem_mul_of (a := [_]) (b := [_]) ?_ ?_) ?_) ?_)
      · exact ofNat_mem_char (by bnd)
      all_goals exact ofNat_mem_byteRange (by bnd) (by bnd)


/-! ## Every encoded scalar is Lean core's encoding of a character -/

theorem toNat_ofNatAux {v : Nat} (hv : v.isValidChar) : (Char.ofNatAux v hv).val.toNat = v := rfl

theorem byte_of_mem_byteRange {lo hi : UInt8} {w : List UInt8}
    (h : w ∈ (byteRange lo hi).matches') :
    ∃ b : UInt8, w = [b] ∧ lo.toNat ≤ b.toNat ∧ b.toNat ≤ hi.toNat := by
  obtain ⟨b, rfl, h₁, h₂⟩ := mem_byteRange.mp h
  exact ⟨b, rfl, UInt8.le_iff_toNat_le.mp h₁, UInt8.le_iff_toNat_le.mp h₂⟩

theorem byte_of_mem_char {a : UInt8} {w : List UInt8} (h : w ∈ (char a).matches') :
    ∃ b : UInt8, w = [b] ∧ a.toNat ≤ b.toNat ∧ b.toNat ≤ a.toNat := ⟨a, h, le_rfl, le_rfl⟩

theorem split_of_mem_mul {P Q : RegularExpression UInt8} {w : List UInt8}
    (h : w ∈ (P * Q).matches') : ∃ a b, a ∈ P.matches' ∧ b ∈ Q.matches' ∧ w = a ++ b := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Language.mem_mul.mp h
  exact ⟨a, b, ha, hb, rfl⟩

/-- Finish a row: the bytes are Lean's encoding of the scalar value `v` they spell. -/
local macro "row" v:term : tactic => `(tactic| (
  refine ⟨Char.ofNatAux $v (by unfold Nat.isValidChar; omega), ?_⟩
  simp only [String.utf8EncodeChar, toNat_ofNatAux]
  split_ifs <;> (try omega) <;> simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true] <;>
    (try refine ⟨?_, ?_⟩) <;> (try refine ⟨?_, ?_⟩) <;> (try refine ⟨?_, ?_⟩) <;>
    apply UInt8.toNat_inj.mp <;> simp only [UInt8.toNat_ofNat', Nat.reducePow] <;> omega))

/-- One byte of a class: a `byteRange` or a `char`, with its bounds. -/
local macro "byte" h:term : term =>
  `(term| by first | exact byte_of_mem_byteRange $h | exact byte_of_mem_char $h)

theorem exists_char_of_mem_scalar {w : List UInt8} (h : w ∈ scalar.matches') :
    ∃ c : Char, String.utf8EncodeChar c = w := by
  simp only [scalar, multibyte, seq2, seq3, seq4, ascii, tail, matches'_add,
    Language.mem_add] at h
  rcases h with h | ((h | (((h | h) | h) | h)) | ((h | h) | h))
  · obtain ⟨b, rfl, -, h₁⟩ := byte_of_mem_byteRange h
    simp only [UInt8.reduceToNat] at *
    row b.toNat
  · obtain ⟨_, _, h₀, h₁, rfl⟩ := split_of_mem_mul h
    obtain ⟨b₀, rfl, l₀, u₀⟩ := byte_of_mem_byteRange h₀
    obtain ⟨b₁, rfl, l₁, u₁⟩ := byte_of_mem_byteRange h₁
    simp only [UInt8.reduceToNat] at *
    row (b₀.toNat - 0xC0) * 64 + (b₁.toNat - 0x80)
  all_goals first
    | (obtain ⟨_, _, ha, h₂, rfl⟩ := split_of_mem_mul h
       obtain ⟨_, _, hb, h₁, rfl⟩ := split_of_mem_mul ha
       obtain ⟨_, _, h₀, h₁', rfl⟩ := split_of_mem_mul hb
       obtain ⟨b₀, rfl, l₀, u₀⟩ := byte h₀
       obtain ⟨b₁, rfl, l₁, u₁⟩ := byte h₁'
       obtain ⟨b₂, rfl, l₂, u₂⟩ := byte h₁
       obtain ⟨b₃, rfl, l₃, u₃⟩ := byte h₂
       simp only [UInt8.reduceToNat] at *
       row (b₀.toNat - 0xF0) * 262144 + (b₁.toNat - 0x80) * 4096 + (b₂.toNat - 0x80) * 64 +
         (b₃.toNat - 0x80))
    | (obtain ⟨_, _, ha, h₂, rfl⟩ := split_of_mem_mul h
       obtain ⟨_, _, h₀, h₁, rfl⟩ := split_of_mem_mul ha
       obtain ⟨b₀, rfl, l₀, u₀⟩ := byte h₀
       obtain ⟨b₁, rfl, l₁, u₁⟩ := byte h₁
       obtain ⟨b₂, rfl, l₂, u₂⟩ := byte h₂
       simp only [UInt8.reduceToNat] at *
       row (b₀.toNat - 0xE0) * 4096 + (b₁.toNat - 0x80) * 64 + (b₂.toNat - 0x80))

/-! ## Sequences: well-formed UTF-8 is exactly `List.utf8Encode` -/

theorem isWellFormed_iff_exists_chars {w : List UInt8} :
    IsWellFormed w ↔ ∃ cs : List Char, w = cs.flatMap String.utf8EncodeChar := by
  rw [Silmaril.Proofs.Formats.Utf8.isWellFormed_iff_flatten]
  constructor
  · rintro ⟨L, rfl, hL⟩
    induction L with
    | nil => exact ⟨[], rfl⟩
    | cons y L ih =>
      obtain ⟨c, hc⟩ := exists_char_of_mem_scalar (hL y (by simp))
      obtain ⟨cs, hcs⟩ := ih fun z hz => hL z (by simp [hz])
      exact ⟨c :: cs, by simp [hc, hcs]⟩
  · rintro ⟨cs, rfl⟩
    refine ⟨cs.map String.utf8EncodeChar, by simp [List.flatMap], ?_⟩
    intro y hy
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hy
    exact utf8EncodeChar_mem_scalar c

theorem isValidUTF8_iff {b : ByteArray} : b.IsValidUTF8 ↔ IsWellFormed b.data.toList := by
  rw [isWellFormed_iff_exists_chars]
  constructor
  · rintro ⟨cs, rfl⟩; exact ⟨cs, rfl⟩
  · rintro ⟨cs, h⟩
    refine ⟨cs, ?_⟩
    rcases b with ⟨⟨l⟩⟩
    simp only [List.utf8Encode]
    simp only at h
    rw [h]

theorem fromUTF8?_isSome_iff {b : ByteArray} :
    (String.fromUTF8? b).isSome ↔ IsWellFormed b.data.toList := by
  rw [← isValidUTF8_iff, String.fromUTF8?]
  split <;> simp_all

end Silmaril.Proofs.Formats.Utf8.Core

end
