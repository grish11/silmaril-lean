module

public import Silmaril.Prelude.Bytes.Format.Defs
public import Silmaril.Prelude.Bytes.Thms
import Silmaril.Proofs.Prelude.Bytes.Digits

/-! Proofs for `Silmaril.Prelude.Bytes.Format.Thms`. `exactKCheck_sound` follows #125's
`cstringCheck_sound`. -/

@[expose] public section

namespace Silmaril.Proofs.Prelude.Bytes

open Silmaril Silmaril.KBytes Silmaril.ByteFormat

theorem exactKCheck_sound (t : KBytes) (a : List UInt8) (h : exactKCheck t a = true) :
    t.toList = a := by
  simp only [exactKCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hw, hl⟩, hr⟩ := h
  have hlen := length_toList t hw
  rw [read_eq t 0 _ hw (by omega), List.drop_zero, List.take_of_length_le (by omega)] at hr
  exact leVal_inj (by omega) hr

theorem exactBCheck_sound (b : ByteArray) (a : List UInt8) (h : exactBCheck b a = true) :
    b.data.toList = a := by
  simp only [exactBCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

theorem all_ne_zero {s : List UInt8} (h : s.all (· != 0) = true) : ∀ c ∈ s, c ≠ 0 := by
  simpa using h

end Silmaril.Proofs.Prelude.Bytes
