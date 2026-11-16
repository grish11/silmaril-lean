module

public import Silmaril.Proofs.Logic.Temporal.CTLStar.FiniteTableau.Local
public import Mathlib.Tactic.Tauto

@[expose] public section
namespace Silmaril.Logic.Temporal.CTLStar.FiniteTableau

/-- Finite backward induction makes the endpoint determine every earlier equation. -/
theorem backward_iff (F G : Nat → Prop) (n : Nat) (last : F n ↔ G n)
    (step : ∀ t, t < n → (F (t+1) ↔ G (t+1)) → (F t ↔ G t)) :
    ∀ t, t ≤ n → (F t ↔ G t) := by
  intro t ht
  exact Nat.decreasingInduction (motive := fun t _ => F t ↔ G t)
    (fun k hk ih => step k hk ih) last ht

theorem until_step {A : Type} (word : Nat → A → Prop) (p q : NNF.Formula A)
    (n t : Nat) (ht : t < n) :
    (p.until q).Holds (some n) word t ↔ q.Holds (some n) word t ∨
      (p.Holds (some n) word t ∧ (p.until q).Holds (some n) word (t+1)) := by
  constructor
  · show (p.until q).Holds (some n) word t → _
    rintro ⟨d, hd, hq, hp⟩
    cases d with
    | zero => exact Or.inl (by simpa using hq)
    | succ d =>
      show q.Holds (some n) word t ∨ _
      right
      refine ⟨by simpa using hp 0 (Nat.zero_lt_succ d), d, ?_, ?_, ?_⟩
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hd
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq
      · intro j hj
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp (j+1) (by omega)
  · show (q.Holds (some n) word t ∨ _) → (p.until q).Holds (some n) word t
    rintro (hq | ⟨hp, d, hd, hq, hrest⟩)
    · exact ⟨0, Nat.le_of_lt ht, hq, fun j hj => (Nat.not_lt_zero j hj).elim⟩
    · show (p.until q).Holds (some n) word t
      refine ⟨d+1, ?_, ?_, ?_⟩
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hd
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq
      · intro j hj
        cases j with
        | zero => simpa using hp
        | succ j => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest j (by omega)

theorem release_step {A : Type} (word : Nat → A → Prop) (p q : NNF.Formula A)
    (n t : Nat) (ht : t < n) :
    (p.release q).Holds (some n) word t ↔ q.Holds (some n) word t ∧
      (p.Holds (some n) word t ∨ (p.release q).Holds (some n) word (t+1)) := by
  classical
  have hd (i : Nat) : (p.release q).Holds (some n) word i ↔
      ¬ (p.dual.until q.dual).Holds (some n) word i := by
    simpa only [NNF.Formula.dual, NNF.Formula.dual_dual] using
      NNF.Formula.holds_dual (some n) word (p.dual.until q.dual) i
  rw [hd t, until_step word p.dual q.dual n t ht]
  simp only [NNF.Formula.holds_dual]
  have hn := hd (t+1)
  tauto

end Silmaril.Logic.Temporal.CTLStar.FiniteTableau
