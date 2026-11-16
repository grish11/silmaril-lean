module

public import Silmaril.Proofs.Logic.Temporal.CTLStar.FiniteTableau.Recurrence

@[expose] public section
namespace Silmaril.Logic.Temporal.CTLStar.FiniteTableau
open LTL.Tableau

/-- Every finite consistent run has the exact semantic root bit at every valid
position. The terminal guard replaces any infinite fairness condition. -/
theorem run_exact {A : Type} (p : NNF.Formula A) (n : Nat) (word : Nat → A → Prop)
    (run : Nat → State (shape p))
    (steps : ∀ t, t < n → Local p (word t) (run t) (run (t+1)))
    (last : End p (word n) (run n)) :
    ∀ t, t ≤ n → (bit (run t) = true ↔ p.Holds (some n) word t) := by
  induction p with
  | pos a | neg a =>
      intro t ht
      rcases lt_or_eq_of_le ht with h | rfl
      · exact steps t h
      · exact last
  | bot =>
      intro t ht
      have hb : bit (run t) = false := by
        rcases lt_or_eq_of_le ht with h | rfl
        · exact steps t h
        · exact last
      simp [hb, NNF.Formula.Holds]
  | top =>
      intro t ht
      have hb : bit (run t) = true := by
        rcases lt_or_eq_of_le ht with h | rfl
        · exact steps t h
        · exact last
      simp [hb, NNF.Formula.Holds]
  | strongNext p hp =>
      show ∀ t, t ≤ n → (bit (run t) = true ↔ (p.strongNext).Holds (some n) word t)
      have child : ∀ t, t ≤ n → (bit (unary (run t)) = true ↔ p.Holds (some n) word t) := hp (fun t => unary (run t)) (fun t ht => (steps t ht).2) last.2
      intro t ht
      rcases lt_or_eq_of_le ht with h | rfl
      · have hv : ValidIndex (some n) (t+1) := h
        simpa only [NNF.Formula.Holds, hv, true_and, (steps t h).1] using child (t+1) h
      · simp only [last.1, Bool.false_eq_true, NNF.Formula.strongNext_at_last]
  | weakNext p hp =>
      show ∀ t, t ≤ n → (bit (run t) = true ↔ (p.weakNext).Holds (some n) word t)
      have child : ∀ t, t ≤ n → (bit (unary (run t)) = true ↔ p.Holds (some n) word t) := hp (fun t => unary (run t)) (fun t ht => (steps t ht).2) last.2
      intro t ht
      rcases lt_or_eq_of_le ht with h | rfl
      · have hv : ValidIndex (some n) (t+1) := h
        simpa only [NNF.Formula.Holds, hv, true_implies, (steps t h).1] using child (t+1) h
      · exact iff_of_true last.1 (NNF.Formula.weakNext_at_last word p _)
  | conj p q hp hq =>
      show ∀ t, t ≤ n → (bit (run t) = true ↔ (p.conj q).Holds (some n) word t)
      have hl : ∀ t, t ≤ n → (bit (left (run t)) = true ↔ p.Holds (some n) word t) := hp (fun t => left (run t)) (fun t ht => (steps t ht).2.1) last.2.1
      have hr : ∀ t, t ≤ n → (bit (right (run t)) = true ↔ q.Holds (some n) word t) := hq (fun t => right (run t)) (fun t ht => (steps t ht).2.2) last.2.2
      intro t ht
      have hb : bit (run t) = (bit (left (run t)) && bit (right (run t))) := by
        rcases lt_or_eq_of_le ht with h | rfl
        · exact (steps t h).1
        · exact last.1
      simpa only [hb, Bool.and_eq_true, NNF.Formula.Holds] using and_congr (hl t ht) (hr t ht)
  | disj p q hp hq =>
      show ∀ t, t ≤ n → (bit (run t) = true ↔ (p.disj q).Holds (some n) word t)
      have hl : ∀ t, t ≤ n → (bit (left (run t)) = true ↔ p.Holds (some n) word t) := hp (fun t => left (run t)) (fun t ht => (steps t ht).2.1) last.2.1
      have hr : ∀ t, t ≤ n → (bit (right (run t)) = true ↔ q.Holds (some n) word t) := hq (fun t => right (run t)) (fun t ht => (steps t ht).2.2) last.2.2
      intro t ht
      have hb : bit (run t) = (bit (left (run t)) || bit (right (run t))) := by
        rcases lt_or_eq_of_le ht with h | rfl
        · exact (steps t h).1
        · exact last.1
      simpa only [hb, Bool.or_eq_true, NNF.Formula.Holds] using or_congr (hl t ht) (hr t ht)
  | «until» p q hp hq =>
      show ∀ t, t ≤ n → (bit (run t) = true ↔ (p.until q).Holds (some n) word t)
      have hl : ∀ t, t ≤ n → (bit (left (run t)) = true ↔ p.Holds (some n) word t) := hp (fun t => left (run t)) (fun t ht => (steps t ht).2.1) last.2.1
      have hr : ∀ t, t ≤ n → (bit (right (run t)) = true ↔ q.Holds (some n) word t) := hq (fun t => right (run t)) (fun t ht => (steps t ht).2.2) last.2.2
      apply backward_iff (fun t => bit (run t) = true) _ n
      · rw [last.1]
        exact (hr n le_rfl).trans (NNF.Formula.until_at_last word p q n).symm
      · intro t ht ih
        rw [(steps t ht).1]
        simp only [Bool.or_eq_true, Bool.and_eq_true]
        rw [hl t (Nat.le_of_lt ht), hr t (Nat.le_of_lt ht), ih]
        exact (until_step word p q n t ht).symm
  | release p q hp hq =>
      show ∀ t, t ≤ n → (bit (run t) = true ↔ (p.release q).Holds (some n) word t)
      have hl : ∀ t, t ≤ n → (bit (left (run t)) = true ↔ p.Holds (some n) word t) := hp (fun t => left (run t)) (fun t ht => (steps t ht).2.1) last.2.1
      have hr : ∀ t, t ≤ n → (bit (right (run t)) = true ↔ q.Holds (some n) word t) := hq (fun t => right (run t)) (fun t ht => (steps t ht).2.2) last.2.2
      apply backward_iff (fun t => bit (run t) = true) _ n
      · rw [last.1]
        exact (hr n le_rfl).trans (NNF.Formula.release_at_last word p q n).symm
      · intro t ht ih
        rw [(steps t ht).1]
        simp only [Bool.or_eq_true, Bool.and_eq_true]
        rw [hl t (Nat.le_of_lt ht), hr t (Nat.le_of_lt ht), ih]
        exact (release_step word p q n t ht).symm

end Silmaril.Logic.Temporal.CTLStar.FiniteTableau
