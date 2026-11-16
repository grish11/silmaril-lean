module

public import Silmaril.Formats.Ascii.Defs
public import Silmaril.Formats.Utf8.Thms

/-! # Proofs: the language of ASCII bytes (`Silmaril.Formats.Ascii.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Ascii

open Silmaril.Formats Silmaril.Formats.Ascii

theorem isAscii_iff {w : List UInt8} : isAscii w = true ↔ w ∈ language := by
  change _ ↔ ∀ b ∈ w, b < 0x80
  simp [isAscii]

theorem toNat_ofNat_of_lt {n : Nat} (h : n < 0x80) : (Char.ofNat n).toNat = n := by
  have hv : n.isValidChar := by unfold Nat.isValidChar; omega
  simp [Char.ofNat, hv, Char.ofNatAux, Char.toNat]

theorem utf8EncodeChar_of_lt {c : Char} (h : c.toNat < 0x80) :
    String.utf8EncodeChar c = [UInt8.ofNat c.toNat] := by
  simp only [Char.toNat] at h
  simp only [String.utf8EncodeChar]
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
  rfl

theorem mem_language_iff_exists_chars {w : List UInt8} :
    w ∈ language ↔
      ∃ cs : List Char, (∀ c ∈ cs, c.toNat < 0x80) ∧ w = cs.flatMap String.utf8EncodeChar := by
  constructor
  · intro h
    refine ⟨w.map fun b => Char.ofNat b.toNat, ?_, ?_⟩
    · intro c hc
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
      have hb' : b.toNat < 0x80 := by
        have := h b hb; simp only [IsAsciiByte, UInt8.lt_iff_toNat_lt] at this; simpa using this
      rw [toNat_ofNat_of_lt hb']; exact hb'
    · induction w with
      | nil => rfl
      | cons a w ih =>
        have ha : a.toNat < 0x80 := by
          have := h a (by simp); simp only [IsAsciiByte, UInt8.lt_iff_toNat_lt] at this
          simpa using this
        have hc : (Char.ofNat a.toNat).toNat = a.toNat := toNat_ofNat_of_lt ha
        simp only [List.map_cons, List.flatMap_cons]
        rw [utf8EncodeChar_of_lt (by omega), hc, ← ih (fun b hb => h b (by simp [hb]))]
        simp
  · rintro ⟨cs, hcs, rfl⟩ b hb
    obtain ⟨c, hc, hb⟩ := List.mem_flatMap.mp hb
    rw [utf8EncodeChar_of_lt (hcs c hc), List.mem_singleton] at hb
    subst hb
    have := hcs c hc
    simp only [IsAsciiByte, UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat]
    simp
    omega

end Silmaril.Proofs.Formats.Ascii

end
