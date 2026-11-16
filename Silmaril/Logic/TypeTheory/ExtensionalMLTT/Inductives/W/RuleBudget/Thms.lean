module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.RuleBudget.Defs

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

/-- One extra finite target universe; an unrestricted budget stays unrestricted. -/
def RuleBudget.succ : RuleBudget → RuleBudget
  | .finite n => .finite (n + 1)
  | .unbounded => .unbounded

/-- Forget the internal representation of the finite-or-unrestricted proof capacity. -/
def RuleBudget.capacity : RuleBudget → WithTop ℕ
  | .finite n => n
  | .unbounded => ⊤

/-- The internal budget admits exactly the public extended-natural universe indices. -/
theorem RuleBudget.allows_iff {budget : RuleBudget} {n : ℕ} :
    budget.Allows n ↔ (n : WithTop ℕ) < budget.capacity := by
  cases budget <;> simp [RuleBudget.Allows, RuleBudget.capacity]

theorem RuleBudget.le_succ (budget : RuleBudget) : budget ≤ budget.succ := by
  cases budget with
  | finite n => exact Nat.le_succ n
  | unbounded => trivial

theorem RuleBudget.Allows.succ {budget : RuleBudget} {n : ℕ} (h : budget.Allows n) :
    budget.succ.Allows n := h.mono budget.le_succ

theorem RuleBudget.Allows.succ_index {budget : RuleBudget} {n : ℕ}
    (h : budget.Allows n) : budget.succ.Allows (n + 1) := by
  cases budget <;> simp_all [RuleBudget.succ, RuleBudget.Allows]

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
