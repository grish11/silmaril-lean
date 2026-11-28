module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorCaseOperands.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.PairSequencing.CaseOperand.Thms

/-! # The earlier operand rule leaves the singleton let₁-case gap -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithLetCase

universe u
variable {Φ : Type u} [HasTy Φ (Ty Empty)]

/-- The exact singleton specialization is independent of Paper with the
constructor-operand rule, already with two constant arms. -/
theorem unit_return_ne :
    ¬ WithConstructorCaseOperands.Eqv (τ := Ty Empty) (Φ := Φ) [Ty.coprod Ty.unit Ty.unit]
      (.let₁ (.case (.var 0) .unit .unit) (.br 0 (.var 0)))
      (.case (.var 0) (.let₁ .unit (.br 0 (.var 0))) (.let₁ .unit (.br 0 (.var 0)))) [Ty.unit] := by
  apply BoundSimulation.Obstruction.PairSequencing.unit_case_return_ne_of_call_sites
  intro Γ L r s h
  cases h <;> first | exact .inl ⟨_, _, _, _, rfl, rfl⟩ | exact .inr ⟨_, _, _, _, _, rfl, rfl⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithLetCase
