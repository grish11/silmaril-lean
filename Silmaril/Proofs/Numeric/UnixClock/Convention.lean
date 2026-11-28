module

public import Silmaril.Numeric.UnixClock.Defs

public section

namespace Silmaril.Proofs.Numeric.UnixClock

open Silmaril.Numeric.UnixClock Set
open scoped ENNReal

theorem worstError_le_iff (a b : Convention) (bound : ℝ≥0∞) :
    a.worstError b ≤ bound ↔ ∀ (t : ℝ) (ha : t ∈ a.domain) (hb : t ∈ b.domain),
      ENNReal.ofReal |a.forward ⟨t, ha⟩ - b.forward ⟨t, hb⟩| ≤ bound := by
  rw [Convention.worstError, iSup_le_iff]
  exact ⟨fun h t ha hb => h ⟨t, ha, hb⟩, fun h t => h t t.property.1 t.property.2⟩

theorem worstError_empty {a b : Convention} (h : Disjoint a.domain b.domain) :
    a.worstError b = 0 := by
  apply le_antisymm _ bot_le
  exact (worstError_le_iff a b 0).mpr fun _ ha hb => False.elim (Set.disjoint_left.mp h ha hb)

theorem worstError_approx (a b : Convention) {bound : ℝ≥0∞} (h : bound < a.worstError b) :
    ∃ (t : ℝ) (ha : t ∈ a.domain) (hb : t ∈ b.domain),
      bound < ENNReal.ofReal |a.forward ⟨t, ha⟩ - b.forward ⟨t, hb⟩| := by
  simpa only [worstError_le_iff, not_forall, not_le] using not_le.mpr h

theorem worstError_eq_top_iff (a b : Convention) :
    a.worstError b = ⊤ ↔ ∀ bound : ℝ, 0 ≤ bound →
      ∃ (t : ℝ) (ha : t ∈ a.domain) (hb : t ∈ b.domain),
        bound < |a.forward ⟨t, ha⟩ - b.forward ⟨t, hb⟩| := by
  constructor
  · intro h bound hbound
    obtain ⟨t, ha, hb, ht⟩ := worstError_approx a b
      (bound := ENNReal.ofReal bound) (by rw [h]; exact ENNReal.ofReal_lt_top)
    exact ⟨t, ha, hb, lt_of_not_ge fun hle => ht.not_ge (ENNReal.ofReal_le_ofReal hle)⟩
  · intro h
    by_contra htop
    obtain ⟨t, ha, hb, ht⟩ := h (a.worstError b).toReal ENNReal.toReal_nonneg
    have hle := (worstError_le_iff a b _).mp le_rfl t ha hb
    exact ht.not_ge ((ENNReal.ofReal_le_iff_le_toReal htop).mp hle)

theorem worstError_eq_sample_iff (a b : Convention) {t : ℝ}
    (ha : t ∈ a.domain) (hb : t ∈ b.domain) :
    a.worstError b = ENNReal.ofReal |a.forward ⟨t, ha⟩ - b.forward ⟨t, hb⟩| ↔
      ∀ (x : ℝ) (hxa : x ∈ a.domain) (hxb : x ∈ b.domain),
        ENNReal.ofReal |a.forward ⟨x, hxa⟩ - b.forward ⟨x, hxb⟩| ≤
          ENNReal.ofReal |a.forward ⟨t, ha⟩ - b.forward ⟨t, hb⟩| := by
  rw [← worstError_le_iff]
  exact ⟨le_of_eq, fun h => le_antisymm h ((worstError_le_iff a b _).mp le_rfl t ha hb)⟩

end Silmaril.Proofs.Numeric.UnixClock
