module

public import Silmaril.Logic.Temporal.LTL.NNF.Recurrence.Defs

@[expose] public section
namespace Silmaril.Logic.Temporal.LTL.NNF.Recurrence
variable {P Q U R : Nat → Prop}

theorem strongUntil_unfold (P Q : Nat → Prop) (n : Nat) :
    strongUntil P Q n ↔ Q n ∨ (P n ∧ strongUntil P Q (n+1)) := by
  constructor
  · rintro ⟨d, hq, hp⟩
    cases d with
    | zero => exact Or.inl (by simpa using hq)
    | succ d =>
      refine Or.inr ⟨by simpa using hp 0 (by omega), d, ?_, ?_⟩
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq
      · intro i hi
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp (i+1) (by omega)
  · rintro (hq | ⟨hp, d, hq, hpre⟩)
    · exact ⟨0, by simpa using hq, fun i hi => False.elim (by omega)⟩
    · refine ⟨d+1, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq, ?_⟩
      intro i hi
      cases i with
      | zero => simpa using hp
      | succ i => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpre i (by omega)

/-- Exact semantic recurrence; unlike a selected release bit, release truth is
itself the greatest compatible solution. -/
theorem release_unfold (P Q : Nat → Prop) (n : Nat) :
    release P Q n ↔ Q n ∧ (P n ∨ release P Q (n+1)) := by
  classical
  constructor
  · show release P Q n → Q n ∧ (P n ∨ release P Q (n+1))
    intro h
    have hq : Q n := by
      rcases h 0 with hq | ⟨i, hi, _⟩
      · simpa using hq
      · omega
    refine ⟨hq, ?_⟩
    by_cases hp : P n
    · exact Or.inl hp
    · right
      intro d
      rcases h (d+1) with hq | ⟨i, hi, hpi⟩
      · exact Or.inl (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq)
      · cases i with
        | zero => exact False.elim (hp (by simpa using hpi))
        | succ i =>
          exact Or.inr ⟨i, by omega, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpi⟩
  · show Q n ∧ (P n ∨ release P Q (n+1)) → release P Q n
    rintro ⟨hq, hp | hn⟩ d
    · cases d with
      | zero => exact Or.inl (by simpa using hq)
      | succ d => exact Or.inr ⟨0, by omega, by simpa using hp⟩
    · cases d with
      | zero => exact Or.inl (by simpa using hq)
      | succ d =>
        rcases hn d with hd | ⟨i, hi, hp⟩
        · exact Or.inl (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hd)
        · exact Or.inr ⟨i+1, by omega, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp⟩

/-- The canonical until truth assignment discharges or becomes inactive
arbitrarily late. This is a statement about each one fixed predicate trace. -/
theorem strongUntil_fair (P Q : Nat → Prop) :
    ∀ t, ∃ s, t ≤ s ∧ (¬ strongUntil P Q s ∨ Q s) := by
  classical
  intro t
  by_cases h : strongUntil P Q t
  · obtain ⟨d, hq, _⟩ := h
    exact ⟨t+d, by omega, Or.inr hq⟩
  · exact ⟨t, le_rfl, Or.inl h⟩

/-- Local unfolding alone permits endless postponement. A recurrent discharge
or inactive bit forces a finite right witness whenever the until bit is selected. -/
theorem until_sound
    (hstep : ∀ t, U t → Q t ∨ (P t ∧ U (t+1)))
    (fair : ∀ t, ∃ s, t ≤ s ∧ (¬ U s ∨ Q s)) :
    ∀ n, U n → strongUntil P Q n := by
  have bounded : ∀ d n, U n → (¬ U (n+d) ∨ Q (n+d)) → strongUntil P Q n := by
    intro d
    induction d with
    | zero =>
      intro n hu he
      rcases he with hn | hq
      · exact False.elim (hn (by simpa using hu))
      · exact (strongUntil_unfold P Q n).mpr (Or.inl (by simpa using hq))
    | succ d ih =>
      intro n hu he
      apply (strongUntil_unfold P Q n).mpr
      rcases hstep n hu with hq | ⟨hp, hn⟩
      · exact Or.inl hq
      · exact Or.inr ⟨hp, ih (n+1) hn (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he)⟩
  intro n hu
  obtain ⟨s, hs, he⟩ := fair n
  exact bounded (s-n) n hu (by simpa [Nat.add_sub_of_le hs] using he)

/-- A selected release bit is sound under its one-step implication. No fairness
is needed, and this does not claim every true release must be selected. -/
theorem release_sound (hstep : ∀ t, R t → Q t ∧ (P t ∨ R (t+1))) :
    ∀ n, R n → release P Q n := by
  have bounded : ∀ d n, R n → Q (n+d) ∨ ∃ i, i < d ∧ P (n+i) := by
    intro d
    induction d with
    | zero =>
      intro n hn
      exact Or.inl (by simpa using (hstep n hn).1)
    | succ d ih =>
      intro n hn
      rcases (hstep n hn).2 with hp | hr
      · exact Or.inr ⟨0, by omega, by simpa using hp⟩
      · rcases ih (n+1) hr with hq | ⟨i, hi, hp⟩
        · exact Or.inl (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq)
        · exact Or.inr ⟨i+1, by omega, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp⟩
  exact fun n hn d => bounded d n hn

/-- Monotone operand replacement supports structural soundness inductions. -/
theorem strongUntil_mono {P' Q' : Nat → Prop} (hp : ∀ n, P n → P' n)
    (hq : ∀ n, Q n → Q' n) (n : Nat) : strongUntil P Q n → strongUntil P' Q' n := by
  rintro ⟨d, hd, hpre⟩
  exact ⟨d, hq _ hd, fun i hi => hp _ (hpre i hi)⟩

theorem release_mono {P' Q' : Nat → Prop} (hp : ∀ n, P n → P' n)
    (hq : ∀ n, Q n → Q' n) (n : Nat) : release P Q n → release P' Q' n := by
  intro h d
  rcases h d with hd | ⟨i, hi, hp'⟩
  · exact Or.inl (hq _ hd)
  · exact Or.inr ⟨i, hi, hp _ hp'⟩

end Silmaril.Logic.Temporal.LTL.NNF.Recurrence
