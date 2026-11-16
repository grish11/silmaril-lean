module

public import Silmaril.Logic.Temporal.CTLStar.Terminal.Defs
public import Mathlib.Tactic.Tauto

@[expose] public section
namespace Silmaril.Logic.Temporal.CTLStar
namespace PathFormula
variable {S : Signature} (M : Model S) (p q : PathFormula S)
  (path : Path M.toModal.accessible) (i : Nat)

theorem weakNext_iff :
    p.weakNext.Holds M path i ↔ (path.Valid (i+1) → p.Holds M path (i+1)) := by
  classical
  simp only [weakNext, Holds]
  tauto

/-- Negating strong next requires weak next of the negated operand. -/
theorem not_next_iff_weakNext_neg :
    (¬ (PathFormula.next p).Holds M path i) ↔
      (PathFormula.neg p).weakNext.Holds M path i := by
  classical
  simp only [weakNext, Holds, not_not]

/-- Release of the negated operands is precisely the negation of strong until. -/
theorem not_until_iff_release_neg :
    (¬ (PathFormula.until p q).Holds M path i) ↔
      ((PathFormula.neg p).release (PathFormula.neg q)).Holds M path i := by
  classical
  simp only [release, Holds, not_not]

theorem next_at_terminal {n : Nat} (h : path.last = some n) :
    ¬ (PathFormula.next p).Holds M path n := by
  intro hn
  have hv := hn.1
  simp only [Path.Valid, ValidIndex, h] at hv
  omega

theorem weakNext_at_terminal {n : Nat} (h : path.last = some n) :
    p.weakNext.Holds M path n := by
  apply (weakNext_iff M p path n).mpr
  intro hv
  simp only [Path.Valid, ValidIndex, h] at hv
  omega

/-- Strong until either discharges now or makes one actual next step. -/
theorem until_unfold (hi : path.Valid i) :
    (PathFormula.until p q).Holds M path i ↔ q.Holds M path i ∨
      (p.Holds M path i ∧ (PathFormula.next (PathFormula.until p q)).Holds M path i) := by
  constructor
  · show (PathFormula.until p q).Holds M path i →
      q.Holds M path i ∨
        (p.Holds M path i ∧ (PathFormula.next (PathFormula.until p q)).Holds M path i)
    rintro ⟨d, hd, hq, hp⟩
    cases d with
    | zero => exact Or.inl (by simpa using hq)
    | succ d =>
      show q.Holds M path i ∨
        (p.Holds M path i ∧ (PathFormula.next (PathFormula.until p q)).Holds M path i)
      right
      refine ⟨by simpa using hp 0 (Nat.zero_lt_succ d), ?_⟩
      refine ⟨path.valid_of_le hd (by omega), d, ?_, ?_, ?_⟩
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hd
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq
      · intro j hj
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp (j+1) (by omega)
  · show (q.Holds M path i ∨
      (p.Holds M path i ∧ (PathFormula.next (PathFormula.until p q)).Holds M path i)) →
        (PathFormula.until p q).Holds M path i
    rintro (hq | ⟨hp, hv, d, hd, hq, hrest⟩)
    · exact ⟨0, by simpa using hi, by simpa using hq,
        fun j hj => (Nat.not_lt_zero j hj).elim⟩
    · show (PathFormula.until p q).Holds M path i
      refine ⟨d+1, ?_, ?_, ?_⟩
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hd
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq
      · intro j hj
        cases j with
        | zero => simpa using hp
        | succ j => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest j (by omega)

/-- Only valid positions constrain release; a finite terminal position is included. -/
theorem release_iff :
    (p.release q).Holds M path i ↔ ∀ d, path.Valid (i+d) →
      q.Holds M path (i+d) ∨ ∃ j, j < d ∧ p.Holds M path (i+j) := by
  classical
  constructor
  · intro h d hd
    by_contra hn
    apply h
    refine ⟨d, hd, ?_, ?_⟩
    · intro hq
      exact hn (Or.inl hq)
    · intro j hj hp
      exact hn (Or.inr ⟨j, hj, hp⟩)
  · intro h ⟨d, hd, hnq, hnp⟩
    rcases h d hd with hq | ⟨j, hj, hp⟩
    · exact hnq hq
    · exact hnp j hj hp

/-- The dual recurrence uses weak next, which also covers a genuine endpoint. -/
theorem release_unfold (hi : path.Valid i) :
    (p.release q).Holds M path i ↔ q.Holds M path i ∧
      (p.Holds M path i ∨ (p.release q).weakNext.Holds M path i) := by
  classical
  change (¬ (PathFormula.until (.neg p) (.neg q)).Holds M path i) ↔ _
  rw [until_unfold M (.neg p) (.neg q) path i hi, weakNext_iff]
  change (¬ (¬ q.Holds M path i ∨ (¬ p.Holds M path i ∧
    (path.Valid (i+1) ∧ (PathFormula.until (.neg p) (.neg q)).Holds M path (i+1))))) ↔
    q.Holds M path i ∧ (p.Holds M path i ∨
      (path.Valid (i+1) → ¬ (PathFormula.until (.neg p) (.neg q)).Holds M path (i+1)))
  tauto

theorem until_at_terminal {n : Nat} (h : path.last = some n) :
    (PathFormula.until p q).Holds M path n ↔ q.Holds M path n := by
  rw [until_unfold M p q path n (by simp [Path.Valid, ValidIndex, h])]
  have hn := next_at_terminal M (PathFormula.until p q) path h
  tauto

theorem release_at_terminal {n : Nat} (h : path.last = some n) :
    (p.release q).Holds M path n ↔ q.Holds M path n := by
  rw [release_unfold M p q path n (by simp [Path.Valid, ValidIndex, h])]
  have hn := weakNext_at_terminal M (p.release q) path h
  tauto

end PathFormula
end Silmaril.Logic.Temporal.CTLStar
