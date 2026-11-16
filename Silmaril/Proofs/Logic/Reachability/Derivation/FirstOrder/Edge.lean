module

public import Silmaril.Logic.Reachability.Derivation.FirstOrder.Edge.Defs

@[expose] public section
namespace Silmaril.Logic.Reachability.Derivation.FirstOrder.Edge
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.FirstOrder.Variables Silmaril.Logic.FirstOrder.FiniteConnectives
variable {Sg : FOL.Signature} (M : FOL.Structure Sg)

theorem sourceSelector_holds {k : Nat} (cfg : Sg.S) (Γ : Fin k → Sg.S)
    (a : (i : Fin k) → M.carrier (Γ i)) (w x : M.carrier cfg) :
    Pattern.localHolds (sourceSelector (Sg := Sg) cfg Γ) M (consAssignment M cfg Γ w a) x ↔ x = w := by
  rfl

/-- The source-selector equality forces the existential snapshot to be w.
No default values or nonempty unrelated sorts are required. -/
theorem ruleFormula_holds {k : Nat} (cfg : Sg.S) (Γ : Fin k → Sg.S)
    (rule : Step.FormulaRule (Sg := Sg) cfg) (a : (i : Fin k) → M.carrier (Γ i))
    (w v : M.carrier cfg) :
    Pattern.localHolds (ruleFormula (Sg := Sg) cfg Γ rule) M (consAssignment M cfg Γ w a) v ↔
      ∃ b, (rule.scheme M).lhs b w ∧ (rule.scheme M).rhs b v := by
  unfold ruleFormula Pattern.localHolds
  refine (existsBlock_holds M cfg (Fin.cases cfg Γ) rule.telescope _ v
    (consAssignment M cfg Γ w a)).trans ?_
  constructor
  · rintro ⟨b, hb⟩
    change (Pattern.localHolds (Step.snapshotSource (Fin.cases cfg Γ) rule.telescope
      (sourceSelector (Sg := Sg) cfg Γ) rule.lhs) M
        (joinAssignment M (consAssignment M cfg Γ w a) rule.telescope b) v ∧
      Pattern.localHolds (liftRule cfg (Fin.cases cfg Γ) rule.telescope rule.rhs) M
        (joinAssignment M (consAssignment M cfg Γ w a) rule.telescope b) v) at hb
    obtain ⟨x, hx, hl⟩ := (Step.snapshotSource_holds M (Fin.cases cfg Γ) rule.telescope
      (sourceSelector (Sg := Sg) cfg Γ) rule.lhs (consAssignment M cfg Γ w a) b v).mp hb.1
    have same : x = w := (sourceSelector_holds M cfg Γ a w x).mp hx
    have hr : (rule.scheme M).rhs b v :=
      (@liftRule_holds Sg M (k + 1) cfg
        (Fin.cases (motive := fun _ : Fin (k + 1) => Sg.S) cfg Γ) rule.telescope rule.rhs
        v (consAssignment M cfg Γ w a) b).mp hb.2
    refine ⟨b, ?_, hr⟩
    simpa only [Step.FormulaRule.scheme, same] using hl
  · rintro ⟨b, hl, hr⟩
    refine ⟨b, ?_⟩
    change (Pattern.localHolds (Step.snapshotSource (Fin.cases cfg Γ) rule.telescope
      (sourceSelector (Sg := Sg) cfg Γ) rule.lhs) M
        (joinAssignment M (consAssignment M cfg Γ w a) rule.telescope b) v ∧
      Pattern.localHolds (liftRule cfg (Fin.cases cfg Γ) rule.telescope rule.rhs) M
        (joinAssignment M (consAssignment M cfg Γ w a) rule.telescope b) v)
    constructor
    · apply (Step.snapshotSource_holds M (Fin.cases cfg Γ) rule.telescope
        (sourceSelector (Sg := Sg) cfg Γ) rule.lhs (consAssignment M cfg Γ w a) b v).mpr
      exact ⟨w, (sourceSelector_holds M cfg Γ a w w).mpr rfl, hl⟩
    · exact (@liftRule_holds Sg M (k + 1) cfg (Fin.cases cfg Γ) rule.telescope rule.rhs
        v (consAssignment M cfg Γ w a) b).mpr hr

/-- Exact one-step correspondence for arbitrary original outer assignments.
The right side is the existing semantic induced relation, not added FOL syntax. -/
theorem edgeFormula_holds {k r : Nat} (cfg : Sg.S) (Γ : Fin k → Sg.S)
    (rules : Fin r → Step.FormulaRule (Sg := Sg) cfg) (a : (i : Fin k) → M.carrier (Γ i))
    (w v : M.carrier cfg) :
    Pattern.localHolds (edgeFormula (Sg := Sg) cfg Γ rules) M (consAssignment M cfg Γ w a) v ↔
      RuleSystem.Induced (Step.schemes M rules) w v := by
  unfold edgeFormula Pattern.localHolds
  rw [finiteOr_holds]
  constructor
  · rintro ⟨p, hp, h⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    obtain ⟨b, hl, hr⟩ := (ruleFormula_holds M cfg Γ (rules i) a w v).mp h
    exact ⟨i, b, hl, hr⟩
  · rintro ⟨i, b, hl, hr⟩
    exact ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩,
      (ruleFormula_holds M cfg Γ (rules i) a w v).mpr ⟨b, hl, hr⟩⟩

theorem edgeFormula_independent_outer {k r : Nat} (cfg : Sg.S) (Γ : Fin k → Sg.S)
    (rules : Fin r → Step.FormulaRule (Sg := Sg) cfg) (a a' : (i : Fin k) → M.carrier (Γ i))
    (w v : M.carrier cfg) :
    Pattern.localHolds (edgeFormula (Sg := Sg) cfg Γ rules) M (consAssignment M cfg Γ w a) v ↔
      Pattern.localHolds (edgeFormula (Sg := Sg) cfg Γ rules) M (consAssignment M cfg Γ w a') v :=
  (edgeFormula_holds M cfg Γ rules a w v).trans (edgeFormula_holds M cfg Γ rules a' w v).symm

end Silmaril.Logic.Reachability.Derivation.FirstOrder.Edge
