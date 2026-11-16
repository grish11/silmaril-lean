module

public import Silmaril.Logic.Kore.Operational.Conditional.FirstOrder.Thms

@[expose] public section
namespace Silmaril.Logic.Kore.Operational.Conditional.FirstOrder.Examples

def ab : Rule := ⟨"a", "b", .zero⟩
def ac : Rule := ⟨"a", "c", .nonzero⟩
def competing : Rule := ⟨"a", "c", .zero⟩

/-- A nonempty capture block and actual negative integers are supported. -/
theorem zero_edge (tail : List String) (counter : Int) :
    Reachability.RuleSystem.Induced
      (Reachability.Derivation.FirstOrder.Step.schemes (model [ab, ac]) (formulaRules [ab, ac]))
      ⟨"a" :: tail, 0, counter⟩ ⟨"b" :: tail, 0, counter⟩ := by
  apply (induced_iff _ _ _).mpr
  exact .rule ab (by simp) ⟨tail, 0, 0, counter⟩ rfl
    (by simp [ab, Guard.Holds, Guard.eval, intEqual])

theorem negative_edge (tail : List String) (counter : Int) :
    Reachability.RuleSystem.Induced
      (Reachability.Derivation.FirstOrder.Step.schemes (model [ab, ac]) (formulaRules [ab, ac]))
      ⟨"a" :: tail, -1, counter⟩ ⟨"c" :: tail, -1, counter⟩ := by
  apply (induced_iff _ _ _).mpr
  exact .rule ac (by simp) ⟨tail, -1, -1, counter⟩ rfl
    (by simp [ac, Guard.Holds, Guard.eval, intEqual])

/-- The as-pattern captures remain independent, so mismatch disables the lhs
at every configuration, even when the zero guard is true. -/
theorem capture_mismatch (tail : List String) (counter : Int) (c : Config) :
    ¬ ((formulaRule [ab] 0).scheme (model [ab])).lhs
      (encodeValuation [ab] ⟨tail, 0, 1, counter⟩) c := by
  rw [lhs_holds]
  simp

/-- Capture coherence alone cannot enable a false guard. -/
theorem disabled_guard (tail : List String) (counter : Int) (c : Config) :
    ¬ ((formulaRule [ab] 0).scheme (model [ab])).lhs
      (encodeValuation [ab] ⟨tail, 1, 1, counter⟩) c := by
  rw [lhs_holds]
  simp [ab, Guard.Holds, Guard.eval, intEqual]

/-- Both enabled competitors survive translation. An exclusivity assertion
would incorrectly discard one actual successor. -/
theorem competing_edges (tail : List String) (counter : Int) :
    Reachability.RuleSystem.Induced
      (Reachability.Derivation.FirstOrder.Step.schemes (model [ab, competing]) (formulaRules [ab, competing]))
      ⟨"a" :: tail, 0, counter⟩ ⟨"b" :: tail, 0, counter⟩ ∧
    Reachability.RuleSystem.Induced
      (Reachability.Derivation.FirstOrder.Step.schemes (model [ab, competing]) (formulaRules [ab, competing]))
      ⟨"a" :: tail, 0, counter⟩ ⟨"c" :: tail, 0, counter⟩ := by
  constructor
  · apply (induced_iff _ _ _).mpr
    exact .rule ab (by simp) ⟨tail, 0, 0, counter⟩ rfl
      (by simp [ab, Guard.Holds, Guard.eval, intEqual])
  · apply (induced_iff _ _ _).mpr
    exact .rule competing (by simp) ⟨tail, 0, 0, counter⟩ rfl
      (by simp [competing, Guard.Holds, Guard.eval, intEqual])

/-- A reached b-state has no successor in the singleton a→b profile. -/
theorem terminal_deadlock (tail : List String) (counter : Int) (d : Config) :
    ¬ Reachability.RuleSystem.Induced
      (Reachability.Derivation.FirstOrder.Step.schemes (model [ab]) (formulaRules [ab]))
      ⟨"b" :: tail, 0, counter⟩ d := by
  rw [induced_iff, step_iff]
  rintro ⟨r, hr, v, _, _, before, _⟩
  have same : r = ab := List.mem_singleton.mp hr
  subst r
  have codes := congrArg Config.code before
  simp [Rule.beforeConfig, ab] at codes

/-- A zero-rule program has no operational edges; no default rule is inserted. -/
theorem empty_deadlock (c d : Config) :
    ¬ Reachability.RuleSystem.Induced
      (Reachability.Derivation.FirstOrder.Step.schemes (model []) (formulaRules [])) c d := by
  rintro ⟨i, _, _, _⟩
  exact i.elim0

end Silmaril.Logic.Kore.Operational.Conditional.FirstOrder.Examples
