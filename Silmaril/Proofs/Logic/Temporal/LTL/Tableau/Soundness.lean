module

public import Silmaril.Proofs.Logic.Temporal.LTL.Tableau.Local
public import Silmaril.Logic.Temporal.LTL.NNF.Recurrence.Thms

@[expose] public section
noncomputable section
open Classical
namespace Silmaril.Logic.Temporal.LTL.Tableau

/-- Soundness only asserts active bits imply truth. In particular an inactive
release bit is not claimed to imply falsity of the greatest semantic solution. -/
theorem active_sound {Atom : Type} (p : NNF.Formula Atom) (word : Nat → Atom → Prop)
    (run : Nat → State (shape p))
    (steps : ∀ t, Local p (word t) (run t) (run (t+1))) (fair : Fair p run) :
    ∀ t, bit (run t) = true → p.Holds word t := by
  induction p with
  | pos a => intro t ht; exact (steps t).mp ht
  | neg a => intro t ht; exact (steps t).mp ht
  | bot => intro t ht; have h : Local .bot (word t) (run t) (run (t+1)) := steps t; change bit (run t) = false at h; rw [h] at ht; cases ht
  | top => intro _ _; trivial
  | next p hp =>
    have child : ∀ t, bit (unary (run t)) = true → p.Holds word t := hp (fun t => unary (run t)) (fun t => (steps t).2)
      (fun i t => fair (.inr i) t)
    intro t ht
    exact child (t+1) ((steps t).1 ▸ ht)
  | conj p q hp hq =>
    show ∀ t, bit (run t) = true → (NNF.Formula.conj p q).Holds word t
    have hl : ∀ t, bit (left (run t)) = true → p.Holds word t := hp (fun t => left (run t)) (fun t => (steps t).2.1)
      (fun i t => fair (.inr (.inl i)) t)
    have hr : ∀ t, bit (right (run t)) = true → q.Holds word t := hq (fun t => right (run t)) (fun t => (steps t).2.2)
      (fun i t => fair (.inr (.inr i)) t)
    intro t ht
    have h : bit (left (run t)) = true ∧ bit (right (run t)) = true := by
      simpa only [(steps t).1, Bool.and_eq_true] using ht
    exact ⟨hl t h.1, hr t h.2⟩
  | disj p q hp hq =>
    show ∀ t, bit (run t) = true → (NNF.Formula.disj p q).Holds word t
    have hl : ∀ t, bit (left (run t)) = true → p.Holds word t := hp (fun t => left (run t)) (fun t => (steps t).2.1)
      (fun i t => fair (.inr (.inl i)) t)
    have hr : ∀ t, bit (right (run t)) = true → q.Holds word t := hq (fun t => right (run t)) (fun t => (steps t).2.2)
      (fun i t => fair (.inr (.inr i)) t)
    intro t ht
    have h : bit (left (run t)) = true ∨ bit (right (run t)) = true := by
      simpa only [(steps t).1, Bool.or_eq_true] using ht
    exact h.elim (fun h => Or.inl (hl t h)) (fun h => Or.inr (hr t h))
  | «until» p q hp hq =>
    show ∀ t, bit (run t) = true → (NNF.Formula.until p q).Holds word t
    have hl : ∀ t, bit (left (run t)) = true → p.Holds word t := hp (fun t => left (run t)) (fun t => (steps t).2.1)
      (fun i t => fair (.inr (.inl i)) t)
    have hr : ∀ t, bit (right (run t)) = true → q.Holds word t := hq (fun t => right (run t)) (fun t => (steps t).2.2)
      (fun i t => fair (.inr (.inr i)) t)
    apply NNF.Recurrence.until_sound
    · intro t ht
      have h : bit (right (run t)) = true ∨
          (bit (left (run t)) = true ∧ bit (run (t+1)) = true) := by
        simpa only [(steps t).1, Bool.or_eq_true, Bool.and_eq_true] using ht
      exact h.elim (fun h => Or.inl (hr t h)) (fun h => Or.inr ⟨hl t h.1, h.2⟩)
    · intro t
      obtain ⟨u, hu, h⟩ : ∃ u, t ≤ u ∧ discharged (.until p q) (run u) (.inl ()) := fair (.inl ()) t
      change bit (run u) = false ∨ bit (right (run u)) = true at h
      refine ⟨u, hu, ?_⟩
      rcases h with h | h
      · exact Or.inl (by rw [h]; decide)
      · exact Or.inr (hr u h)
  | release p q hp hq =>
    show ∀ t, bit (run t) = true → (NNF.Formula.release p q).Holds word t
    have hl : ∀ t, bit (left (run t)) = true → p.Holds word t := hp (fun t => left (run t)) (fun t => (steps t).2.1)
      (fun i t => fair (.inr (.inl i)) t)
    have hr : ∀ t, bit (right (run t)) = true → q.Holds word t := hq (fun t => right (run t)) (fun t => (steps t).2.2)
      (fun i t => fair (.inr (.inr i)) t)
    apply NNF.Recurrence.release_sound
    intro t ht
    have h : bit (right (run t)) = true ∧
        (bit (left (run t)) = true ∨ bit (run (t+1)) = true) := by
      simpa only [(steps t).1, Bool.and_eq_true, Bool.or_eq_true] using ht
    exact ⟨hr t h.1, h.2.elim (fun h => Or.inl (hl t h)) Or.inr⟩

end Silmaril.Logic.Temporal.LTL.Tableau
