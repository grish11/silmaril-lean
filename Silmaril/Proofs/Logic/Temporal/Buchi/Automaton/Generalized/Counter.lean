module

public import Silmaril.Logic.Temporal.Buchi.Automaton.Generalized.Defs

@[expose] public section
noncomputable section
open Classical
namespace Silmaril.Logic.Temporal.Buchi.Automaton.Generalized

private theorem advance_mono {k : Nat} (hit : Fin k → Prop) (c : Fin (k+1))
    (h : c.val < k) : c.val ≤ (advance hit c).val := by
  simp only [advance, h, ↓reduceDIte]
  split <;> simp_all

private theorem advance_barrier {k : Nat} (hit : Fin k → Prop) (c : Fin (k+1))
    (i : Fin k) (h : c.val ≤ i.val) (hn : ¬ hit i) : (advance hit c).val ≤ i.val := by
  have hc : c.val < k := lt_of_le_of_lt h i.isLt
  simp only [advance, hc, ↓reduceDIte]
  split
  · rename_i hh
    have hne : c.val ≠ i.val := by
      intro he
      have he' : (⟨c.val, hc⟩ : Fin k) = i := Fin.ext he
      exact hn (he' ▸ hh)
    change c.val+1 ≤ i.val
    omega
  · exact h

/-- Generic finite monitor theorem. Requirements and phase sequence are independent
of any automaton syntax. No initial-phase assumption is needed for recurrence. -/
theorem recurrent_iff {k : Nat} (hit : Nat → Fin k → Prop)
    (c : Nat → Fin (k+1)) (step : ∀ t, c (t+1) = advance (hit t) (c t)) :
    (∀ t, ∃ u, t ≤ u ∧ (c u).val = k) ↔
      ∀ i, ∀ t, ∃ u, t ≤ u ∧ hit u i := by
  constructor
  · show (∀ t, ∃ u, t ≤ u ∧ (c u).val = k) →
        ∀ i, ∀ t, ∃ u, t ≤ u ∧ hit u i
    intro recur i t
    by_contra hn
    have absent : ∀ u, t ≤ u → ¬ hit u i := by
      intro u hu hh
      exact hn ⟨u, hu, hh⟩
    obtain ⟨u, hu, hdone⟩ := recur t
    have hz : c (u+1) = 0 := by
      rw [step]
      simp [advance, hdone]
    have bound : ∀ d, (c (u+1+d)).val ≤ i.val := by
      intro d
      induction d with
      | zero => simp [hz]
      | succ d ih =>
        rw [show u+1+(d+1) = (u+1+d)+1 by omega, step]
        exact advance_barrier _ _ i ih (absent _ (by omega))
    obtain ⟨v, hv, hvdone⟩ := recur (u+1)
    have hb : (c (u+1+(v-(u+1)))).val ≤ i.val := bound (v-(u+1))
    rw [Nat.add_sub_of_le hv, hvdone] at hb
    exact (Nat.not_le_of_lt i.isLt) hb
  · show (∀ i, ∀ t, ∃ u, t ≤ u ∧ hit u i) →
        ∀ t, ∃ u, t ≤ u ∧ (c u).val = k
    intro fair t
    by_contra hn
    have nodone : ∀ u, t ≤ u → (c u).val < k := by
      intro u hu
      have hb : (c u).val < k+1 := (c u).isLt
      have hne : (c u).val ≠ k := fun he => hn ⟨u, hu, he⟩
      omega
    have mono : ∀ u v, t ≤ u → u ≤ v → (c u).val ≤ (c v).val := by
      intro u v htu huv
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le huv
      induction d with
      | zero => rfl
      | succ d ih =>
        apply (ih (by omega)).trans
        rw [show u+(d+1) = (u+d)+1 by omega, step]
        exact advance_mono _ _ (nodone _ (by omega))
    have progress : ∀ j, j ≤ k → ∃ u, t ≤ u ∧ j ≤ (c u).val := by
      intro j hj
      induction j with
      | zero => exact ⟨t, le_rfl, Nat.zero_le _⟩
      | succ j ih =>
        show ∃ u, t ≤ u ∧ j+1 ≤ (c u).val
        obtain ⟨u, hu, hcu⟩ := ih (by omega)
        obtain ⟨v, hv, hh⟩ := fair ⟨j, by omega⟩ u
        have hcv : j ≤ (c v).val := hcu.trans (mono u v hu hv)
        refine ⟨v+1, by omega, ?_⟩
        rw [step]
        by_cases he : (c v).val = j
        · have hc : (c v).val < k := nodone v (by omega)
          simp only [advance, hc, ↓reduceDIte]
          have hh' : hit v ⟨(c v).val, hc⟩ := by simpa only [he] using hh
          simp only [hh', ↓reduceIte]
          change j+1 ≤ (c v).val+1
          omega
        · exact (by omega : j+1 ≤ (c v).val).trans
            (advance_mono _ _ (nodone _ (by omega)))
    obtain ⟨u, hu, hb⟩ := progress k le_rfl
    exact (Nat.not_le_of_lt (nodone u hu)) hb

end Silmaril.Logic.Temporal.Buchi.Automaton.Generalized
