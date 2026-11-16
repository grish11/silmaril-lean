module

public import Silmaril.Logic.Reachability.Derivation.FirstOrder.Step.Thms

@[expose] public section
namespace Silmaril.Logic.Reachability.Derivation.FirstOrder.Edge
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.FirstOrder.Variables Silmaril.Logic.FirstOrder.FiniteConnectives
variable {Sg : FOL.Signature}

/-- The distinguished configuration equals a captured source at slot1. -/
def sourceSelector {k : Nat} (cfg : Sg.S) (Γ : Fin k → Sg.S) :
    Pattern Sg cfg (Fin.cases cfg Γ) := .eq (.var 0) (.var 1)

/-- Bind one rule's own variables. The snapshotted source and current outcome
use the same rule block; the source configuration remains an outer capture. -/
def ruleFormula {k : Nat} (cfg : Sg.S) (Γ : Fin k → Sg.S)
    (rule : Step.FormulaRule (Sg := Sg) cfg) : Pattern Sg cfg (Fin.cases cfg Γ) :=
  existsBlock cfg (Fin.cases cfg Γ) rule.telescope
    (.and (Step.snapshotSource (Fin.cases cfg Γ) rule.telescope
      (sourceSelector (Sg := Sg) cfg Γ) rule.lhs)
      (liftRule cfg (Fin.cases cfg Γ) rule.telescope rule.rhs))

/-- Finite disjunction of operational rule instances, expressed solely using
existing FOL syntax. No transition relation symbol is added to the signature. -/
def edgeFormula {k r : Nat} (cfg : Sg.S) (Γ : Fin k → Sg.S)
    (rules : Fin r → Step.FormulaRule (Sg := Sg) cfg) : Pattern Sg cfg (Fin.cases cfg Γ) :=
  finiteOr (List.ofFn fun i => ruleFormula (Sg := Sg) cfg Γ (rules i))

end Silmaril.Logic.Reachability.Derivation.FirstOrder.Edge
