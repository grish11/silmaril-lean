module

public import Silmaril.Logic.Temporal.LTL.NNF.Recurrence.Thms

@[expose] public section
namespace Silmaril.Logic.Temporal.LTL.NNF.Recurrence.Examples

/-- An endlessly selected until bit can satisfy local consistency. -/
theorem forever_postponed_step : ∀ _t : Nat,
    True → False ∨ (True ∧ True) := by
  intro _ _
  exact Or.inr ⟨True.intro, True.intro⟩

theorem forever_postponed_rejected (n : Nat) :
    ¬ strongUntil (fun _ => True) (fun _ => False) n := by
  rintro ⟨_, h, _⟩
  exact h

/-- The recurrent discharge/inactive condition rejects that very local trace. -/
theorem forever_postponed_not_fair :
    ¬ (∀ t : Nat, ∃ s, t ≤ s ∧ (¬ True ∨ False)) := by
  intro h
  obtain ⟨_, _, hn | hf⟩ := h 0
  · exact hn True.intro
  · exact hf

/-- A finite selected obligation remains live through time three and discharges. -/
theorem discharge_at_three (n : Nat) (hn : n ≤ 3) :
    strongUntil (fun t => t < 3) (fun t => t = 3) n := by
  apply until_sound (U := fun t => t ≤ 3) ?_ ?_ n hn
  · intro t ht
    by_cases he : t = 3
    · exact Or.inl he
    · exact Or.inr ⟨by omega, by omega⟩
  · intro t
    refine ⟨max t 3, le_max_left _ _, ?_⟩
    by_cases he : max t 3 = 3
    · exact Or.inr he
    · exact Or.inl (by omega)

/-- Greatest release semantics allows q forever without any p witness. -/
theorem release_forever (n : Nat) : release (fun _ => False) (fun _ => True) n := by
  apply release_sound (R := fun _ => True) ?_ n True.intro
  intro _ _
  exact ⟨True.intro, Or.inr True.intro⟩

/-- Even p now does not excuse a false q now. -/
theorem release_requires_current_right (n : Nat) :
    ¬ release (fun _ => True) (fun _ => False) n := by
  intro h
  rcases h 0 with hf | ⟨i, hi, _⟩
  · exact hf
  · omega

/-- The false selected bit satisfies the implication recurrence, yet release
truth holds everywhere. Thus selected-bit soundness cannot be an iff. -/
theorem release_bit_under_approximates (n : Nat) :
    (∀ _t : Nat, False → True ∧ (False ∨ False)) ∧
      release (fun _ => False) (fun _ => True) n ∧ ¬ False := by
  exact ⟨fun _ h => False.elim h, release_forever n, id⟩

end Silmaril.Logic.Temporal.LTL.NNF.Recurrence.Examples
