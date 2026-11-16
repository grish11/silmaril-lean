module

public import Silmaril.Logic.Kore.Operational.Conditional.FirstOrder.Defs

@[expose] public section
namespace Silmaril.Logic.Kore.Operational.Conditional.FirstOrder
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.FirstOrder.Variables

@[simp] theorem decode_encode (rules : List Rule) (v : Valuation) :
    decodeValuation rules (encodeValuation rules v) = v := by
  cases v
  rfl

@[simp] theorem encode_decode (rules : List Rule) (b : BlockAssignment (model rules) telescope) :
    encodeValuation rules (decodeValuation rules b) = b := by
  rcases b with ⟨tail, x, captured, counter, u⟩
  cases u
  rfl

theorem configTerm_before_eval (rules : List Rule) (i : Fin rules.length) (v : Valuation) (c : Config) :
    (configTerm rules i false).eval (model rules).toAlgebra
      (consAssignment (model rules) FSort.config (blockContext emptyContext telescope) c (assignment rules v)) =
      (rules.get i).beforeConfig v := by
  rfl

theorem configTerm_after_eval (rules : List Rule) (i : Fin rules.length) (v : Valuation) (c : Config) :
    (configTerm rules i true).eval (model rules).toAlgebra
      (consAssignment (model rules) FSort.config (blockContext emptyContext telescope) c (assignment rules v)) =
      (rules.get i).afterConfig v := by
  rfl

/-- Both hooks compile to equality/negation syntax, rather than semantic atoms. -/
theorem guard_holds (rules : List Rule) (g : Guard) (v : Valuation) (c : Config) :
    Reachability.Derivation.FirstOrder.Pattern.localHolds (guardFormula rules g) (model rules) (assignment rules v) c ↔ g.Holds v.x := by
  cases g
  · change (v.x = (0 : Int)) ↔ Guard.Holds .zero v.x
    simp [Guard.Holds, Guard.eval, intEqual]
  · change (v.x ≠ (0 : Int)) ↔ Guard.Holds .nonzero v.x
    simp [Guard.Holds, Guard.eval, intEqual]

theorem lhs_holds (rules : List Rule) (i : Fin rules.length) (v : Valuation) (c : Config) :
    ((formulaRule rules i).scheme (model rules)).lhs (encodeValuation rules v) c ↔
      v.x = v.capturedVal ∧ (rules.get i).guard.Holds v.x ∧ c = (rules.get i).beforeConfig v := by
  change (v.x = v.capturedVal ∧
    Reachability.Derivation.FirstOrder.Pattern.localHolds (guardFormula rules (rules.get i).guard) (model rules) (assignment rules v) c ∧
    c = (rules.get i).beforeConfig v) ↔ _
  rw [guard_holds]

theorem rhs_holds (rules : List Rule) (i : Fin rules.length) (v : Valuation) (c : Config) :
    ((formulaRule rules i).scheme (model rules)).rhs (encodeValuation rules v) c ↔
      c = (rules.get i).afterConfig v := by
  rfl

/-- All installed indices participate. One block assignment is shared by both
endpoints; no rule-selection or exclusivity premise is used. -/
theorem induced_iff (rules : List Rule) (c d : Config) :
    Reachability.RuleSystem.Induced (Reachability.Derivation.FirstOrder.Step.schemes (model rules) (formulaRules rules)) c d ↔
      Step rules c d := by
  rw [step_iff]
  constructor
  · rintro ⟨i, b, hl, hr⟩
    let v := decodeValuation rules b
    have hb : encodeValuation rules v = b := encode_decode rules b
    rw [← hb] at hl hr
    obtain ⟨coherent, enabled, before⟩ := (lhs_holds rules i v c).mp hl
    exact ⟨rules.get i, List.get_mem rules i, v, coherent, enabled, before,
      (rhs_holds rules i v d).mp hr⟩
  · rintro ⟨r, member, v, coherent, enabled, before, after⟩
    obtain ⟨n, hn, he⟩ := List.mem_iff_getElem.mp member
    let i : Fin rules.length := ⟨n, hn⟩
    have hi : rules.get i = r := he
    refine ⟨i, encodeValuation rules v, ?_, ?_⟩
    · exact (lhs_holds rules i v c).mpr (by simpa only [hi] using And.intro coherent ⟨enabled, before⟩)
    · exact (rhs_holds rules i v d).mpr (by simpa only [hi] using after)

/-- The existing FOL edge formula denotes exactly the independent operational
Step relation, with arbitrary unrelated claim captures retained. -/
theorem edgeFormula_holds (rules : List Rule) {k : Nat} (Γ : Fin k → FSort)
    (a : (i : Fin k) → (model rules).carrier (Γ i)) (c d : Config) :
    Reachability.Derivation.FirstOrder.Pattern.localHolds (Sg := signature rules) (cfg := FSort.config)
      (Γ := Fin.cases FSort.config Γ)
      (Reachability.Derivation.FirstOrder.Edge.edgeFormula (Sg := signature rules) FSort.config Γ (formulaRules rules)) (model rules)
      (consAssignment (model rules) FSort.config Γ c a) d ↔ Step rules c d :=
  (Reachability.Derivation.FirstOrder.Edge.edgeFormula_holds (model rules) FSort.config Γ (formulaRules rules) a c d).trans
    (induced_iff rules c d)

/-- Program specialization retains every installed axiom, including competitors.
A CheckedProgram value alone does not assert that check accepted its bytes. -/
theorem checked_induced_iff (p : CheckedProgram) (c d : Config) :
    Reachability.RuleSystem.Induced (Reachability.Derivation.FirstOrder.Step.schemes (model p.axioms) (formulaRules p.axioms)) c d ↔
      Step p.axioms c d := induced_iff p.axioms c d

end Silmaril.Logic.Kore.Operational.Conditional.FirstOrder
