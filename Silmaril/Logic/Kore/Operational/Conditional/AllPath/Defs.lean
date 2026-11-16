module

public import Silmaril.Logic.Kore.Operational.Conditional.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.Operational.Conditional.AllPath

/-- All enabled competitors at the same source state have the same target state.
This is a rule-set hypothesis, not a consequence of installed membership. -/
def Exclusive (rules : List Rule) (r : Rule) : Prop :=
  ∀ s ∈ rules, s.before = r.before → ∀ x : Int,
    r.guard.Holds x → s.guard.Holds x → s.after = r.after

/-- A finite, decidable sufficient condition exploiting the two disjoint guards. -/
def SyntacticExclusive (rules : List Rule) (r : Rule) : Prop :=
  ∀ s ∈ rules, s.before = r.before → s.after = r.after ∨ s.guard ≠ r.guard

instance (rules : List Rule) (r : Rule) : Decidable (SyntacticExclusive rules r) :=
  inferInstanceAs (Decidable (∀ s ∈ rules, s.before = r.before →
    s.after = r.after ∨ s.guard ≠ r.guard))

/-- Existing all-path finite-complete-path partial correctness, with original
source captures, precondition and singleton postcondition. -/
def compileAll (r : Rule) : Reachability.Sentence KSort.config signature :=
  ⟨4, context, .allPath, r.pre, r.post⟩

end Silmaril.Logic.Kore.Operational.Conditional.AllPath
