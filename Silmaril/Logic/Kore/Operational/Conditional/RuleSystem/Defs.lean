module

public import Silmaril.Logic.Kore.Operational.Conditional.Thms
public import Silmaril.Logic.Reachability.RuleSystem.Thms

@[expose] public section
namespace Silmaril.Logic.Kore.Operational.Conditional.RuleSystem

/-- Installed rule indices retain membership; parameters retain all four captures. -/
def schemes (rules : List Rule) : {r : Rule // r ∈ rules} → Reachability.RuleSystem.Scheme Config :=
  fun r =>
    { Parameters := Valuation
      lhs := fun v c => v.x = v.capturedVal ∧ r.val.guard.Holds v.x ∧
        c = r.val.beforeConfig v
      rhs := fun v c => c = r.val.afterConfig v }

end Silmaril.Logic.Kore.Operational.Conditional.RuleSystem
