module

public import Silmaril.Logic.Reachability.AllPath.Defs

@[expose] public section
namespace Silmaril.Logic.Reachability

variable {W : Type} {R : W → W → Prop} {Q I P : W → Prop}

/-- A genuine finite complete path cannot avoid a progress invariant's target.
The induction follows the given path, not a selected deterministic execution. -/
theorem AllPathInvariant.sound (h : AllPathInvariant R Q I) :
    ∀ w, I w → AllPartial R Q w := by
  intro w hw n
  induction n generalizing w with
  | zero =>
      intro path h0 hsteps hterminal
      rcases h.progress w hw with hq | ⟨⟨v, hv⟩, _⟩
      · exact ⟨0, Nat.zero_le _, h0.symm ▸ hq⟩
      · exact False.elim (hterminal v (h0.symm ▸ hv))
  | succ n ih =>
      intro path h0 hsteps hterminal
      rcases h.progress w hw with hq | ⟨_, hclosed⟩
      · exact ⟨0, Nat.zero_le _, h0.symm ▸ hq⟩
      · have hfirst : R w (path 1) := h0 ▸ hsteps 0 (Nat.zero_lt_succ n)
        have hnext : I (path 1) := hclosed _ hfirst
        have htail : ∀ i, i < n → R (path (i + 1)) (path ((i + 1) + 1)) := by
          intro i hi
          exact hsteps (i + 1) (Nat.succ_lt_succ hi)
        obtain ⟨i, hi, hq⟩ := ih (path 1) hnext (fun i => path (i + 1)) rfl htail hterminal
        exact ⟨i + 1, Nat.succ_le_succ hi, hq⟩

/-- A non-target state satisfying all-path partial reachability passes that
property to every actual successor. Prefixing retains the complete path. -/
theorem AllPartial.successor {w v : W} (h : AllPartial R Q w)
    (not_target : ¬ Q w) (edge : R w v) : AllPartial R Q v := by
  intro n path h0 hsteps hterminal
  let prefixedPath : Nat → W := fun i => Nat.casesOn i w path
  have hp : ∀ i, i < n + 1 → R (prefixedPath i) (prefixedPath (i + 1)) := by
    intro i hi
    cases i with
    | zero =>
        change R w (path 0)
        rw [h0]
        exact edge
    | succ i =>
        change R (path i) (path (i + 1))
        exact hsteps i (Nat.lt_of_succ_lt_succ hi)
  have ht : ∀ u, ¬ R (prefixedPath (n + 1)) u := hterminal
  obtain ⟨i, hi, hq⟩ := h (n + 1) prefixedPath rfl hp ht
  cases i with
  | zero => exact False.elim (not_target hq)
  | succ i => exact ⟨i, Nat.le_of_succ_le_succ hi, hq⟩

/-- All-path partial reachability itself is the greatest local progress
invariant. No finite branching, determinism or termination premise is needed. -/
theorem allPartial_invariant (R : W → W → Prop) (Q : W → Prop) :
    AllPathInvariant R Q (AllPartial R Q) := by
  classical
  refine ⟨?_⟩
  intro w hw
  by_cases hq : Q w
  · exact Or.inl hq
  · apply Or.inr
    have progress : ∃ v, R w v := by
      by_contra hnone
      have terminal : ∀ v, ¬ R w v := by
        intro v hv
        exact hnone ⟨v, hv⟩
      exact hq ((allPartial_deadlock R Q w terminal).mp hw)
    exact ⟨progress, fun v hv => hw.successor hq hv⟩

/-- Guarded circularity is an exact semantic proof principle for finite-complete
all-path partial reachability; target-free divergence is admitted intentionally. -/
theorem allPartial_iff_invariant (R : W → W → Prop) (Q : W → Prop) (w : W) :
    AllPartial R Q w ↔ ∃ I : W → Prop, I w ∧ AllPathInvariant R Q I := by
  constructor
  · intro h
    exact ⟨AllPartial R Q, h, allPartial_invariant R Q⟩
  · rintro ⟨I, hw, hI⟩
    exact hI.sound w hw

/-- A precondition may enter a shared circular invariant; every branch must
progress or reach the target, including at states reached after prior steps. -/
theorem allPartial_of_invariant (hpre : ∀ w, P w → I w)
    (hI : AllPathInvariant R Q I) : ∀ w, P w → AllPartial R Q w :=
  fun w hw => hI.sound w (hpre w hw)

end Silmaril.Logic.Reachability
