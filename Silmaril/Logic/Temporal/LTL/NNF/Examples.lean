module

public import Silmaril.Logic.Temporal.LTL.NNF.Thms

@[expose] public section
namespace Silmaril.Logic.Temporal.LTL.NNF.Examples

/-- Nested negation crosses next and both temporal operators. -/
def nested : LTL.Formula Bool :=
  .not (.until (.next (.atom false)) (.not (.until (.atom true) (.not (.atom false)))))

theorem nested_syntax : normalize false nested =
    .release (.next (.neg false)) (.until (.pos true) (.neg false)) := rfl

/-- The false atom is always true and the true atom always false. The inner
until cannot finish, so the enclosing release fails at the current time. -/
def constantWord (_ : Nat) (a : Bool) : Prop := a = false

theorem nested_rejected (n : Nat) : ¬ (normalize false nested).Holds constantWord n := by
  intro h
  have hnow := h 0
  change (∃ d, (¬ constantWord (n+0+d) false) ∧
    ∀ i, i < d → constantWord (n+0+i) true) ∨
    (∃ i, i < 0 ∧ ¬ constantWord (n+i+1) false) at hnow
  rcases hnow with ⟨d, hd, _⟩ | ⟨i, hi, _⟩
  · exact hd rfl
  · exact Nat.not_lt_zero i hi

theorem nested_source_rejected (n : Nat) :
    ¬ nested.Holds (ULift.up constantWord) n := by
  intro h
  exact nested_rejected n ((normalize_positive (ULift.up constantWord) nested n).mpr h)

/-- On the opposite constant word, the inner until finishes immediately at
all times, so the nested release holds forever. -/
theorem nested_accepted (n : Nat) :
    (normalize false nested).Holds (fun _ a => a = true) n := by
  intro d
  left
  exact ⟨0, by simp [normalize, Formula.Holds], fun i hi => False.elim (Nat.not_lt_zero i hi)⟩

/-- Strong until cannot accept an infinite postponement of its right operand. -/
theorem strong_until_rejected {Atom : Type} (word : Nat → Atom → Prop) (n : Nat) :
    ¬ (Formula.until .top .bot).Holds word n := by
  rintro ⟨d, hd, _⟩
  exact hd

/-- Release does not require its left operand to occur if its right holds forever. -/
theorem release_forever {Atom : Type} (word : Nat → Atom → Prop) (n : Nat) :
    (Formula.release .bot .top).Holds word n := by
  intro d
  exact Or.inl trivial

/-- Release requires its right operand even at the time the left first holds. -/
theorem release_requires_now {Atom : Type} (word : Nat → Atom → Prop) (n : Nat) :
    ¬ (Formula.release .top .bot).Holds word n := by
  intro h
  rcases h 0 with h | ⟨i, hi, _⟩
  · exact h
  · exact Nat.not_lt_zero i hi

/-- Implication and arbitrary negation disappear from emitted syntax. -/
theorem negated_implication_syntax :
    normalize true (LTL.Formula.imp (.next (.atom false))
      (.not (.until (.atom true) (.atom false)))) =
      .conj (.next (.pos false)) (.until (.pos true) (.pos false)) := rfl

/-- A noninjective atom map can turn a satisfiable Boolean distinction into
p ∧ ¬p; normalization still commutes exactly with the map. -/
theorem collapsed_atoms_rejected (word : Nat → Unit → Prop) (n : Nat) :
    ¬ (normalize false ((LTL.Formula.and (.atom false) (.not (.atom true))).map
      (fun _ : Bool => ()))).Holds word n := by
  change ¬ (word n () ∧ ¬ word n ())
  exact fun h => h.2 h.1

end Silmaril.Logic.Temporal.LTL.NNF.Examples
