module

public import Silmaril.SSA.Peggy.Worked.StrengthReduction.Defs
import Silmaril.SSA.Peggy.Worked.EvalScale.Thms
import Silmaril.SSA.PEG.Rules.Thms

public section

namespace Silmaril.Proofs.SSA.Peggy.Worked.StrengthReduction

open Silmaril.SSA.PEG
open Silmaril.SSA.Peggy.Worked
open Silmaril.SSA.Peggy.Worked.StrengthReduction
open Silmaril.SSA.RVSDG (Tuple)

universe u v x

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat} {g : Graph P params results n l}
variable {m : Interpretation.{u,v,x} P} {env : Tuple m.Value params} {values : g.Valuation m}
variable {ops : Profile P}

private theorem bind_feedback (law : Law m ops) (a : Option (m.Value .count)) :
    (a.bind (fun v => m.run ops.step (.cons v .nil))).bind (fun next =>
      m.run ops.scale (.cons law.factorValue (.cons next .nil))) =
    (a.bind (fun v => m.run ops.scale (.cons law.factorValue (.cons v .nil)))).bind (fun scaled =>
      m.run ops.add (.cons law.factorValue (.cons scaled .nil))) := by
  cases a with
  | none => rfl
  | some a => exact law.feedback a

/-- The scaled stream already solves the additive θ equation. The only
recursive read in the successor case is at the preceding index. -/
theorem scaled_recurrence (solves : g.Solves m env values) (law : Law m ops)
    {scaled factor counter initial update bump : Ref g.sort .count} {loop : Fin l}
    (scaleNode : Rules.HasNode scaled (.op ops.scale) (.cons factor (.cons counter .nil)))
    (factorNode : Rules.HasNode factor (.op ops.factor) .nil)
    (thetaNode : Rules.HasNode counter (.theta loop) (.cons initial (.cons update .nil)))
    (baseNode : Rules.HasNode initial (.op ops.base) .nil)
    (stepNode : Rules.HasNode update (.op ops.step) (.cons counter .nil))
    (bumpNode : Rules.HasNode bump (.op ops.add) (.cons factor (.cons scaled .nil)))
    (i : Index l) :
    Rules.readRef values scaled i =
      match i loop with
      | 0 => Rules.readRef values initial i
      | k + 1 => Rules.readRef values bump (i.set loop k) := by
  have fixed (j : Index l) : Rules.readRef values factor j = some law.factorValue :=
    (Rules.at_label solves factorNode j).trans law.definedFactor
  have base (j : Index l) : Rules.readRef values initial j = some law.baseValue :=
    (Rules.at_label solves baseNode j).trans law.definedBase
  cases h : i loop with
  | zero =>
    rw [EvalScale.binary_at solves scaleNode, fixed, Rules.theta_zero solves thetaNode h, base]
    exact law.fixedBase
  | succ k =>
    let prev := i.set loop k
    rw [EvalScale.binary_at solves scaleNode, fixed, Rules.theta_succ solves thetaNode h]
    change (Rules.readRef values update prev).bind (fun v =>
      m.run ops.scale (.cons law.factorValue (.cons v .nil))) = Rules.readRef values bump prev
    rw [Rules.unary_at solves stepNode, EvalScale.binary_at solves bumpNode, fixed]
    have oldScale := EvalScale.binary_at solves scaleNode prev
    rw [fixed] at oldScale
    rw [oldScale]
    exact bind_feedback law _

end Silmaril.Proofs.SSA.Peggy.Worked.StrengthReduction
