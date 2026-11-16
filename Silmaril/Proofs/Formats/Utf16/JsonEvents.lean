module

public import Silmaril.Formats.Utf16.Thms
public import Silmaril.Formats.JsonEvents.Scalar.Defs

/-! # Proofs: `JsonEvents.Utf16.WellFormed` is `Utf16.WellFormedUnits`
(`Silmaril.Formats.Utf16.JsonEvents.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Utf16.JsonEvents

open Silmaril.Formats.Utf16

theorem isHigh_iff (u : UInt16) : Silmaril.Formats.JsonEvents.Utf16.isHigh u = true ↔ IsHigh u := by
  simp [Silmaril.Formats.JsonEvents.Utf16.isHigh, IsHigh]

theorem isLow_iff (u : UInt16) : Silmaril.Formats.JsonEvents.Utf16.isLow u = true ↔ IsLow u := by
  simp [Silmaril.Formats.JsonEvents.Utf16.isLow, IsLow]

theorem isLow_eq (u : UInt16) :
    Silmaril.Formats.JsonEvents.Utf16.isLow u = decide (IsLow u) := by
  rw [Bool.eq_iff_iff, isLow_iff, decide_eq_true_iff]

theorem wellFormed_eq (us : List UInt16) :
    Silmaril.Formats.JsonEvents.Utf16.wellFormed us = wellFormedUnitsB us := by
  induction us using wellFormedUnitsB.induct with
  | case1 => rfl
  | case2 u =>
    simp only [Silmaril.Formats.JsonEvents.Utf16.wellFormed, wellFormedUnitsB]
    by_cases hh : IsHigh u
    · have hs : IsSurrogate u := ⟨hh.1, UInt16.le_trans hh.2 (by decide)⟩
      simp [(isHigh_iff u).mpr hh, hs]
    · have hh' : Silmaril.Formats.JsonEvents.Utf16.isHigh u = false := by
        simpa [← Bool.not_eq_true] using (isHigh_iff u).not.mpr hh
      have : IsSurrogate u ↔ IsLow u := by
        simp only [IsSurrogate, IsLow, IsHigh, not_and, UInt16.not_le] at hh ⊢
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by
            rw [UInt16.le_iff_toNat_le] at h1 ⊢
            have := hh h1; rw [UInt16.lt_iff_toNat_lt] at this; simp at this h1 ⊢; omega, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨UInt16.le_trans (by decide) h1, h2⟩
      simp [hh', ← isLow_iff, this]
  | case3 u v us hh ih =>
    simp only [decide_eq_true_eq] at hh
    simp [Silmaril.Formats.JsonEvents.Utf16.wellFormed, wellFormedUnitsB, (isHigh_iff u).mpr hh,
      hh, ih, isLow_eq]
  | case4 u v us hh ih =>
    simp only [decide_eq_true_eq] at hh
    have hh' : Silmaril.Formats.JsonEvents.Utf16.isHigh u = false := by
      simpa [← Bool.not_eq_true] using (isHigh_iff u).not.mpr hh
    have : IsSurrogate u ↔ IsLow u := by
      simp only [IsSurrogate, IsLow, IsHigh, not_and, UInt16.not_le] at hh ⊢
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by
          rw [UInt16.le_iff_toNat_le] at h1 ⊢
          have := hh h1; rw [UInt16.lt_iff_toNat_lt] at this; simp at this h1 ⊢; omega, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨UInt16.le_trans (by decide) h1, h2⟩
    have ih' := ih
    simp only [Silmaril.Formats.JsonEvents.Utf16.wellFormed] at ih' ⊢
    simp [wellFormedUnitsB, hh, hh', ← ih, ← isLow_iff, this]

end Silmaril.Proofs.Formats.Utf16.JsonEvents

end
