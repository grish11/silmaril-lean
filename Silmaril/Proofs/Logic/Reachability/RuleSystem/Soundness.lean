module

public import Silmaril.Logic.Reachability.RuleSystem.Defs

@[expose] public section
namespace Silmaril.Logic.Reachability.RuleSystem

variable {W ι : Type} {rules : ι → Scheme W} {P Q : W → Prop}

theorem progress (wellDefined : WeaklyWellDefined rules) (cover : Covers rules P)
    (w : W) (hw : P w) : ∃ v, Induced rules w v := by
  obtain ⟨i, a, ha⟩ := cover w hw
  obtain ⟨v, hv⟩ := wellDefined i a w ha
  exact ⟨v, i, a, ha, hv⟩

theorem successors (closed : SuccessorsIn rules P Q) {w v : W}
    (hw : P w) (edge : Induced rules w v) : Q v := by
  obtain ⟨i, a, ha, hb⟩ := edge
  exact closed i a w v hw ha hb

/-- Semantic Step fragment of RTA 2014 Fig.1. Different enabled rules may
produce different targets; every target must satisfy Q. -/
theorem step_sound (wellDefined : WeaklyWellDefined rules) (cover : Covers rules P)
    (closed : SuccessorsIn rules P Q) : ∀ w, P w → AllPartial (Induced rules) Q w := by
  apply allPartial_of_invariant (I := fun w => P w ∨ Q w)
  · intro w hw
    exact Or.inl hw
  · constructor
    intro w hw
    rcases hw with hp | hq
    · exact Or.inr ⟨progress wellDefined cover w hp,
        fun v edge => Or.inr (successors closed hp edge)⟩
    · exact Or.inl hq

theorem Certificate.invariant {n : Nat} (c : Certificate rules Q n)
    (wellDefined : WeaklyWellDefined rules) :
    AllPathInvariant (Induced rules) Q (fun w => Q w ∨ ∃ j, c.node j w) := by
  constructor
  intro w hw
  classical
  by_cases hq : Q w
  · exact Or.inl hq
  · obtain ⟨j, hj⟩ := hw.resolve_left hq
    exact Or.inr ⟨progress wellDefined (c.cover j) w ⟨hj, hq⟩,
      fun v edge => Silmaril.Logic.Reachability.RuleSystem.successors
        (c.successors j) ⟨hj, hq⟩ edge⟩

theorem Certificate.sound {n : Nat} (c : Certificate rules Q n)
    (wellDefined : WeaklyWellDefined rules) {w : W} (entry : Q w ∨ ∃ j, c.node j w) :
    AllPartial (Induced rules) Q w :=
  (c.invariant wellDefined).sound w entry

end Silmaril.Logic.Reachability.RuleSystem
