module

public import Silmaril.Formats.Utf8.Defs

/-! # Proofs: the language of well-formed UTF-8 bytes (`Silmaril.Formats.Utf8.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Utf8

open Silmaril.Formats.Utf8 RegularExpression

theorem mem_anyOf {l : List UInt8} {w : List UInt8} :
    w ∈ (anyOf l).matches' ↔ ∃ b ∈ l, w = [b] := by
  induction l with
  | nil => simp [anyOf, matches', Language.notMem_zero]
  | cons a l ih =>
    simp only [anyOf, List.foldr_cons] at ih ⊢
    rw [← plus_def, matches', Language.mem_add, ih]
    simp only [List.mem_cons, exists_eq_or_imp]
    exact or_congr Iff.rfl Iff.rfl

theorem mem_rangeList {lo hi b : UInt8} : b ∈ rangeList lo hi ↔ lo ≤ b ∧ b ≤ hi := by
  simp only [rangeList, List.mem_map, List.mem_range, UInt8.le_iff_toNat_le]
  constructor
  · rintro ⟨i, hi', rfl⟩
    have := lo.toNat_lt; have := hi.toNat_lt
    simp only [UInt8.toNat_ofNat', Nat.reducePow]
    omega
  · rintro ⟨h₁, h₂⟩
    refine ⟨b.toNat - lo.toNat, by omega, ?_⟩
    apply UInt8.toNat_inj.mp
    have := b.toNat_lt
    simp only [UInt8.toNat_ofNat', Nat.reducePow]
    omega

theorem mem_byteRange {lo hi : UInt8} {w : List UInt8} :
    w ∈ (byteRange lo hi).matches' ↔ ∃ b, w = [b] ∧ lo ≤ b ∧ b ≤ hi := by
  rw [byteRange, mem_anyOf]
  simp only [mem_rangeList]
  constructor
  · rintro ⟨b, hb, rfl⟩; exact ⟨b, rfl, hb⟩
  · rintro ⟨b, rfl, hb⟩; exact ⟨b, hb, rfl⟩

theorem mem_word {l w : List UInt8} : w ∈ (word l).matches' ↔ w = l := by
  induction l generalizing w with
  | nil => simp [word, matches', Language.mem_one]
  | cons a l ih =>
    simp only [word, List.foldr_cons] at ih ⊢
    rw [← comp_def, matches', Language.mem_mul]
    simp only [matches', ih]
    constructor
    · rintro ⟨_, rfl, _, rfl, rfl⟩; rfl
    · rintro rfl; exact ⟨_, rfl, _, rfl, rfl⟩

theorem isWellFormed_iff {w : List UInt8} : isWellFormed w = true ↔ IsWellFormed w :=
  rmatch_iff_matches' _ _

theorem isWellFormed_iff_flatten {w : List UInt8} :
    IsWellFormed w ↔ ∃ L : List (List UInt8), w = L.flatten ∧ ∀ y ∈ L, y ∈ scalar.matches' := by
  rw [IsWellFormed, language, wellFormed, matches', Language.mem_kstar]

theorem isWellFormed_nil : IsWellFormed [] :=
  isWellFormed_iff_flatten.mpr ⟨[], rfl, by simp⟩

theorem isWellFormed_append {a b : List UInt8} (ha : IsWellFormed a) (hb : IsWellFormed b) :
    IsWellFormed (a ++ b) := by
  obtain ⟨L, rfl, hL⟩ := isWellFormed_iff_flatten.mp ha
  obtain ⟨M, rfl, hM⟩ := isWellFormed_iff_flatten.mp hb
  refine isWellFormed_iff_flatten.mpr ⟨L ++ M, by simp, ?_⟩
  intro y hy
  rcases List.mem_append.mp hy with h | h
  exacts [hL y h, hM y h]

theorem scalar_isWellFormed {w : List UInt8} (h : w ∈ scalar.matches') : IsWellFormed w :=
  isWellFormed_iff_flatten.mpr ⟨[w], by simp, by simpa using h⟩

theorem mem_ascii {w : List UInt8} : w ∈ ascii.matches' ↔ ∃ b, w = [b] ∧ b < 0x80 := by
  rw [ascii, mem_byteRange]
  constructor
  · rintro ⟨b, rfl, -, h⟩
    exact ⟨b, rfl, by
      rw [UInt8.lt_iff_toNat_lt]; rw [UInt8.le_iff_toNat_le] at h; simp at h ⊢; omega⟩
  · rintro ⟨b, rfl, h⟩
    exact ⟨b, rfl, UInt8.le_iff_toNat_le.mpr (by simp), by
      rw [UInt8.le_iff_toNat_le]; rw [UInt8.lt_iff_toNat_lt] at h; simp at h ⊢; omega⟩

theorem isWellFormed_of_ascii {w : List UInt8} (h : ∀ b ∈ w, b < 0x80) : IsWellFormed w := by
  induction w with
  | nil => exact isWellFormed_nil
  | cons a w ih =>
    have ha : IsWellFormed [a] :=
      scalar_isWellFormed (by
        rw [scalar, ← plus_def, matches', Language.mem_add]
        exact Or.inl (mem_ascii.mpr ⟨a, rfl, h a (by simp)⟩))
    exact isWellFormed_append (a := [a]) ha (ih fun b hb => h b (by simp [hb]))

end Silmaril.Proofs.Formats.Utf8

end
