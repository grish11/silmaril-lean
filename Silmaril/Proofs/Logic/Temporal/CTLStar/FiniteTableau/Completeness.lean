module

public import Silmaril.Proofs.Logic.Temporal.CTLStar.FiniteTableau.Soundness

@[expose] public section
noncomputable section
open Classical
namespace Silmaril.Logic.Temporal.CTLStar.FiniteTableau
open LTL.Tableau

theorem truth_local {A : Type} (p : NNF.Formula A) (n : Nat) (word : Nat → A → Prop)
    (t : Nat) (ht : t < n) :
    Local p (word t) (truth p n word t) (truth p n word (t+1)) := by
  induction p with
  | pos a | neg a => simp only [Local, truth_bit, NNF.Formula.Holds]
  | bot => simp [Local, truth, bit, subformula, NNF.Formula.Holds]
  | top => simp [Local, truth, bit, subformula, NNF.Formula.Holds]
  | strongNext p hp =>
      simp only [Local, truth_strongNext]
      refine ⟨?_, hp⟩
      apply Bool.eq_iff_iff.mpr
      have hv : ValidIndex (some n) (t+1) := ht
      simp only [truth_bit, NNF.Formula.Holds, hv, true_and]
  | weakNext p hp =>
      simp only [Local, truth_weakNext]
      refine ⟨?_, hp⟩
      apply Bool.eq_iff_iff.mpr
      have hv : ValidIndex (some n) (t+1) := ht
      simp only [truth_bit, NNF.Formula.Holds, hv, true_implies]
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
      exact until_step word p q n t ht
  | release p q hp hq =>
      simp only [Local, truth_release_left, truth_release_right]
      refine ⟨?_, hp, hq⟩
      apply Bool.eq_iff_iff.mpr
      simp only [truth_bit, Bool.or_eq_true, Bool.and_eq_true]
      exact release_step word p q n t ht

theorem truth_end {A : Type} (p : NNF.Formula A) (n : Nat) (word : Nat → A → Prop) :
    End p (word n) (truth p n word n) := by
  induction p with
  | pos a | neg a => simp only [End, truth_bit, NNF.Formula.Holds]
  | bot => simp [End, truth, bit, subformula, NNF.Formula.Holds]
  | top => simp [End, truth, bit, subformula, NNF.Formula.Holds]
  | strongNext p hp =>
      simp only [End, truth_strongNext]
      refine ⟨?_, hp⟩
      apply Bool.eq_false_iff.mpr
      intro h
      exact NNF.Formula.strongNext_at_last word p n ((truth_bit _ _ _ _).mp h)
  | weakNext p hp =>
      simp only [End, truth_weakNext]
      exact ⟨(truth_bit _ _ _ _).mpr (NNF.Formula.weakNext_at_last word p n), hp⟩
  | conj p q hp hq =>
      simp only [End, truth_conj_left, truth_conj_right]
      refine ⟨?_, hp, hq⟩
      apply Bool.eq_iff_iff.mpr
      simp only [truth_bit, Bool.and_eq_true, NNF.Formula.Holds]
  | disj p q hp hq =>
      simp only [End, truth_disj_left, truth_disj_right]
      refine ⟨?_, hp, hq⟩
      apply Bool.eq_iff_iff.mpr
      simp only [truth_bit, Bool.or_eq_true, NNF.Formula.Holds]
  | «until» p q hp hq =>
      simp only [End, truth_until_left, truth_until_right]
      refine ⟨?_, hp, hq⟩
      apply Bool.eq_iff_iff.mpr
      simp only [truth_bit]
      exact NNF.Formula.until_at_last word p q n
  | release p q hp hq =>
      simp only [End, truth_release_left, truth_release_right]
      refine ⟨?_, hp, hq⟩
      apply Bool.eq_iff_iff.mpr
      simp only [truth_bit]
      exact NNF.Formula.release_at_last word p q n

end Silmaril.Logic.Temporal.CTLStar.FiniteTableau
