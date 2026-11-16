module

public import Silmaril.Formats.Utf16.Defs

/-! # Proofs: the languages of well-formed UTF-16 bytes (`Silmaril.Formats.Utf16.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Utf16

open Silmaril.Formats.Utf16

/-! ## Code units and bytes -/

theorem units_serialize (e : Endian) (us : List UInt16) : units e (serialize e us) = some us := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    have hu := u.toNat_lt
    simp only [serialize, List.flatMap_cons] at ih ⊢
    cases e <;>
    · simp only [unitBytes, List.cons_append, List.nil_append, units, ih, Option.map_some,
        Option.some.injEq, List.cons.injEq, and_true]
      apply UInt16.toNat_inj.mp
      simp only [UInt16.toNat_ofNat', UInt8.toNat_ofNat']
      omega

theorem serialize_of_units {e : Endian} {w : List UInt8} {us : List UInt16}
    (h : units e w = some us) : w = serialize e us := by
  induction w using units.induct e generalizing us with
  | case1 => simp only [units, Option.some.injEq] at h; subst h; rfl
  | case2 => simp [units] at h
  | case3 a b t ih =>
    simp only [units] at h
    obtain ⟨vs, hvs, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [ih hvs]
    have ha := a.toNat_lt
    have hb := b.toNat_lt
    cases e <;>
    · simp only [serialize, List.flatMap_cons, unitBytes, List.cons_append, List.nil_append,
        List.cons.injEq, and_true]
      constructor <;>
      · apply UInt8.toNat_inj.mp
        simp only [UInt16.toNat_ofNat', UInt8.toNat_ofNat']
        omega

theorem units_eq_some_iff {e : Endian} {w : List UInt8} {us : List UInt16} :
    units e w = some us ↔ w = serialize e us :=
  ⟨serialize_of_units, fun h => h ▸ units_serialize e us⟩

/-! ## Well-formed code units -/

theorem isHigh_iff {u : UInt16} : IsHigh u ↔ 0xD800 ≤ u.toNat ∧ u.toNat ≤ 0xDBFF := by
  simp [IsHigh, UInt16.le_iff_toNat_le]

theorem isLow_iff {u : UInt16} : IsLow u ↔ 0xDC00 ≤ u.toNat ∧ u.toNat ≤ 0xDFFF := by
  simp [IsLow, UInt16.le_iff_toNat_le]

theorem isSurrogate_iff {u : UInt16} : IsSurrogate u ↔ 0xD800 ≤ u.toNat ∧ u.toNat ≤ 0xDFFF := by
  simp [IsSurrogate, UInt16.le_iff_toNat_le]

theorem wellFormedUnits_singleton {u : UInt16} : WellFormedUnits [u] ↔ ¬ IsSurrogate u := by
  constructor
  · rintro (_ | ⟨hs, _⟩); exact hs
  · intro hs; exact .single hs .nil

theorem wellFormedUnits_cons_cons {u v : UInt16} {us : List UInt16} :
    WellFormedUnits (u :: v :: us) ↔
      (IsHigh u ∧ IsLow v ∧ WellFormedUnits us) ∨
        (¬ IsSurrogate u ∧ WellFormedUnits (v :: us)) := by
  constructor
  · intro h
    cases h with
    | single hs hw => exact Or.inr ⟨hs, hw⟩
    | pair hh hl hw => exact Or.inl ⟨hh, hl, hw⟩
  · rintro (⟨hh, hl, hw⟩ | ⟨hs, hw⟩)
    · exact .pair hh hl hw
    · exact .single hs hw

theorem wellFormedUnitsB_iff {us : List UInt16} :
    wellFormedUnitsB us = true ↔ WellFormedUnits us := by
  induction us using wellFormedUnitsB.induct with
  | case1 => simp only [wellFormedUnitsB, true_iff]; exact .nil
  | case2 u =>
    simp only [wellFormedUnitsB, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
      wellFormedUnits_singleton]
  | case3 u v us hh ih =>
    simp only [wellFormedUnitsB, hh, ite_true, Bool.and_eq_true, decide_eq_true_eq, ih,
      wellFormedUnits_cons_cons]
    simp only [decide_eq_true_eq] at hh
    have : IsSurrogate u := by rw [isSurrogate_iff]; rw [isHigh_iff] at hh; omega
    simp [hh, this]
  | case4 u v us hh ih =>
    simp only [wellFormedUnitsB, hh, Bool.false_eq_true, ite_false, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, ih, wellFormedUnits_cons_cons]
    simp only [decide_eq_true_eq] at hh
    simp [hh]

theorem isWellFormed_iff {e : Endian} {w : List UInt8} :
    isWellFormed e w = true ↔ w ∈ language e := by
  change _ ↔ ∃ us, WellFormedUnits us ∧ w = serialize e us
  unfold isWellFormed
  split
  · rename_i us h
    rw [wellFormedUnitsB_iff]
    constructor
    · intro hw; exact ⟨us, hw, serialize_of_units h⟩
    · rintro ⟨vs, hw, rfl⟩
      rw [units_serialize, Option.some.injEq] at h
      exact h ▸ hw
  · rename_i h
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro us _ hw
    rw [hw, units_serialize] at h
    exact absurd h (by simp)

/-! ## The encoding form (D91) -/

theorem toNat_ofNat_of_isValidChar {n : Nat} (h : n.isValidChar) : (Char.ofNat n).toNat = n := by
  simp [Char.ofNat, h, Char.ofNatAux, Char.toNat]

theorem char_toNat_valid (c : Char) : c.toNat < 0xD800 ∨ (0xDFFF < c.toNat ∧ c.toNat < 0x110000) := by
  have := c.valid
  simp only [UInt32.isValidChar, Nat.isValidChar] at this
  simp only [Char.toNat]
  omega

theorem encodeChar_wellFormed (c : Char) : WellFormedUnits (encodeChar c) := by
  have hc := char_toNat_valid c
  unfold encodeChar
  split
  · refine .single (fun hs => ?_) .nil
    rw [isSurrogate_iff] at hs
    simp only [UInt16.toNat_ofNat'] at hs
    omega
  · refine .pair ?_ ?_ .nil
    · rw [isHigh_iff]; simp only [UInt16.toNat_ofNat']; omega
    · rw [isLow_iff]; simp only [UInt16.toNat_ofNat']; omega

theorem wellFormedUnits_append {us vs : List UInt16} (hu : WellFormedUnits us)
    (hv : WellFormedUnits vs) : WellFormedUnits (us ++ vs) := by
  induction hu with
  | nil => exact hv
  | single hs _ ih => exact .single hs ih
  | pair hh hl _ ih => exact .pair hh hl ih

theorem encodeUnits_wellFormed (cs : List Char) : WellFormedUnits (encodeUnits cs) := by
  induction cs with
  | nil => exact .nil
  | cons c cs ih =>
    simp only [encodeUnits, List.flatMap_cons] at ih ⊢
    exact wellFormedUnits_append (encodeChar_wellFormed c) ih

theorem exists_chars_of_wellFormedUnits {us : List UInt16} (h : WellFormedUnits us) :
    ∃ cs, us = encodeUnits cs := by
  induction h with
  | nil => exact ⟨[], rfl⟩
  | @single u us hs _ ih =>
    obtain ⟨cs, rfl⟩ := ih
    rw [isSurrogate_iff] at hs
    have hu := u.toNat_lt
    have hv : u.toNat.isValidChar := by unfold Nat.isValidChar; omega
    refine ⟨Char.ofNat u.toNat :: cs, ?_⟩
    have hn := toNat_ofNat_of_isValidChar hv
    simp only [encodeUnits, List.flatMap_cons, encodeChar, hn]
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    simp
  | @pair hi lo us hh hl _ ih =>
    obtain ⟨cs, rfl⟩ := ih
    rw [isHigh_iff] at hh
    rw [isLow_iff] at hl
    have hv : (0x10000 + (hi.toNat - 0xD800) * 0x400 + (lo.toNat - 0xDC00)).isValidChar := by
      unfold Nat.isValidChar; omega
    refine ⟨Char.ofNat (0x10000 + (hi.toNat - 0xD800) * 0x400 + (lo.toNat - 0xDC00)) :: cs, ?_⟩
    have hn := toNat_ofNat_of_isValidChar hv
    simp only [encodeUnits, List.flatMap_cons, encodeChar, hn]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true]
    constructor <;>
    · apply UInt16.toNat_inj.mp
      simp only [UInt16.toNat_ofNat']
      omega

theorem wellFormedUnits_iff_exists_chars {us : List UInt16} :
    WellFormedUnits us ↔ ∃ cs, us = encodeUnits cs :=
  ⟨exists_chars_of_wellFormedUnits, fun ⟨cs, h⟩ => h ▸ encodeUnits_wellFormed cs⟩

theorem mem_language_iff_exists_chars {e : Endian} {w : List UInt8} :
    w ∈ language e ↔ ∃ cs, w = serialize e (encodeUnits cs) := by
  change (∃ us, WellFormedUnits us ∧ w = serialize e us) ↔ _
  constructor
  · rintro ⟨us, hw, rfl⟩
    obtain ⟨cs, rfl⟩ := exists_chars_of_wellFormedUnits hw
    exact ⟨cs, rfl⟩
  · rintro ⟨cs, rfl⟩
    exact ⟨_, encodeUnits_wellFormed cs, rfl⟩

theorem encodeChar_injective : Function.Injective encodeChar := by
  intro c d h
  have hc := char_toNat_valid c
  have hd := char_toNat_valid d
  apply Char.toNat_inj.mp
  unfold encodeChar at h
  split at h <;> split at h
  · simp only [List.cons.injEq, and_true] at h
    have := congrArg UInt16.toNat h
    simp only [UInt16.toNat_ofNat'] at this
    omega
  · simp at h
  · simp at h
  · simp only [List.cons.injEq, and_true] at h
    have h1 := congrArg UInt16.toNat h.1
    have h2 := congrArg UInt16.toNat h.2
    simp only [UInt16.toNat_ofNat'] at h1 h2
    omega

end Silmaril.Proofs.Formats.Utf16

end
