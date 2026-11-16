module

public import Silmaril.Proofs.Logic.Temporal.LTL.Tableau.Soundness

@[expose] public section
noncomputable section
open Classical
namespace Silmaril.Logic.Temporal.LTL.Tableau

/-- The canonical semantic truth assignment satisfies every local equation,
including greatest release; this does not constrain arbitrary inactive bits. -/
theorem truth_local {Atom : Type} (p : NNF.Formula Atom) (word : Nat → Atom → Prop)
    (t : Nat) : Local p (word t) (truth p word t) (truth p word (t+1)) := by
  induction p with
  | pos a => simp only [Local, truth_bit, NNF.Formula.Holds]
  | neg a => simp only [Local, truth_bit, NNF.Formula.Holds]
  | bot => simp [Local, truth, bit, subformula, NNF.Formula.Holds]
  | top => simp [Local, truth, bit, subformula, NNF.Formula.Holds]
  | next p hp =>
    simp only [Local, truth_unary]
    refine ⟨?_, hp⟩
    apply Bool.eq_iff_iff.mpr
    simp only [truth_bit, NNF.Formula.Holds]
  | conj p q hp hq =>
    simp only [Local, truth_conj_left, truth_conj_right]
    refine ⟨?_, hp, hq⟩
    apply Bool.eq_iff_iff.mpr
    simp only [truth_bit, Bool.and_eq_true, NNF.Formula.Holds]
  | disj p q hp hq =>
    simp only [Local, truth_disj_left, truth_disj_right]
    refine ⟨?_, hp, hq⟩
    apply Bool.eq_iff_iff.mpr
    simp only [truth_bit, Bool.or_eq_true, NNF.Formula.Holds]
  | «until» p q hp hq =>
    simp only [Local, truth_until_left, truth_until_right]
    refine ⟨?_, hp, hq⟩
    apply Bool.eq_iff_iff.mpr
    simp only [truth_bit, Bool.or_eq_true, Bool.and_eq_true]
    exact NNF.Recurrence.strongUntil_unfold _ _ t
  | release p q hp hq =>
    simp only [Local, truth_release_left, truth_release_right]
    refine ⟨?_, hp, hq⟩
    apply Bool.eq_iff_iff.mpr
    simp only [truth_bit, Bool.or_eq_true, Bool.and_eq_true]
    exact NNF.Recurrence.release_unfold _ _ t

/-- Every canonical until is inactive or discharged arbitrarily late. The full
family also includes trivially true entries for non-until occurrences. -/
theorem truth_fair {Atom : Type} (p : NNF.Formula Atom) (word : Nat → Atom → Prop) :
    Fair p (truth p word) := by
  induction p with
  | pos a => exact fun _ t => ⟨t, le_rfl, trivial⟩
  | neg a => exact fun _ t => ⟨t, le_rfl, trivial⟩
  | bot => exact fun _ t => ⟨t, le_rfl, trivial⟩
  | top => exact fun _ t => ⟨t, le_rfl, trivial⟩
  | next p hp =>
    intro i t
    rcases i with u | i
    · exact ⟨t, le_rfl, trivial⟩
    · simpa only [discharged, truth_unary] using hp i t
  | conj p q hp hq =>
    intro i t
    rcases i with u | (i | i)
    · exact ⟨t, le_rfl, trivial⟩
    · simpa only [discharged, truth_conj_left] using hp i t
    · simpa only [discharged, truth_conj_right] using hq i t
  | disj p q hp hq =>
    intro i t
    rcases i with u | (i | i)
    · exact ⟨t, le_rfl, trivial⟩
    · simpa only [discharged, truth_disj_left] using hp i t
    · simpa only [discharged, truth_disj_right] using hq i t
  | «until» p q hp hq =>
    show Fair (.until p q) (truth (.until p q) word)
    intro i t
    rcases i with u | (i | i)
    · show ∃ s, t ≤ s ∧ discharged (.until p q) (truth (.until p q) word s) (.inl u)
      obtain ⟨s, hs, h⟩ := NNF.Recurrence.strongUntil_fair (p.Holds word) (q.Holds word) t
      refine ⟨s, hs, ?_⟩
      change bit (truth (.until p q) word s) = false ∨ bit (truth q word s) = true
      rcases h with h | h
      · left
        cases he : bit (truth (.until p q) word s)
        · rfl
        · exact False.elim (h ((truth_bit _ _ _).mp he))
      · exact Or.inr ((truth_bit _ _ _).mpr h)
    · simpa only [discharged, truth_until_left] using hp i t
    · simpa only [discharged, truth_until_right] using hq i t
  | release p q hp hq =>
    intro i t
    rcases i with u | (i | i)
    · exact ⟨t, le_rfl, trivial⟩
    · simpa only [discharged, truth_release_left] using hp i t
    · simpa only [discharged, truth_release_right] using hq i t

end Silmaril.Logic.Temporal.LTL.Tableau
