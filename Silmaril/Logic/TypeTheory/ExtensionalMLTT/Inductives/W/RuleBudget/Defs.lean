module

public import Mathlib.Order.WithBot

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

/-- A finite common proof budget, or no common finite restriction.
A dedicated type keeps the natural-number embedding definitionally transparent. -/
inductive RuleBudget where
  | finite (levels : ℕ)
  | unbounded

@[reducible] instance : Coe ℕ RuleBudget := ⟨RuleBudget.finite⟩
@[reducible] instance (n : ℕ) : OfNat RuleBudget n := ⟨RuleBudget.finite n⟩

/-- Finite budgets keep the original strict rule bound; the apex permits every index. -/
abbrev RuleBudget.Allows (budget : RuleBudget) (index : ℕ) : Prop :=
  match budget with
  | .unbounded => True
  | .finite levels => index < levels

instance : Preorder RuleBudget where
  le a b := match a, b with
    | _, .unbounded => True
    | .unbounded, .finite _ => False
    | .finite n, .finite m => n ≤ m
  le_refl a := by cases a <;> simp
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp_all; omega

/-- Enlarge a rule budget without changing the rule's universe index. -/
theorem RuleBudget.Allows.mono {small large : RuleBudget} (h : small ≤ large)
    {index : ℕ} (hi : small.Allows index) : large.Allows index := by
  cases small with
  | unbounded =>
    cases large with
    | unbounded => trivial
    | finite large => exact False.elim h
  | finite small =>
    cases large with
    | unbounded => trivial
    | finite large => exact lt_of_lt_of_le hi h

/-- Two admitted indices have an admitted maximum. -/
theorem RuleBudget.Allows.max {budget : RuleBudget} {a b : ℕ}
    (ha : budget.Allows a) (hb : budget.Allows b) : budget.Allows (max a b) := by
  cases budget with
  | unbounded => trivial
  | finite levels => exact max_lt ha hb

/-- Arithmetic in a finite budget, with the unrestricted branch discharged directly. -/
macro "budget_omega" : tactic =>
  `(tactic| first | omega |
    (cases $(Lean.mkIdent `levels):term <;> simp_all only [RuleBudget.Allows] <;> omega))

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
