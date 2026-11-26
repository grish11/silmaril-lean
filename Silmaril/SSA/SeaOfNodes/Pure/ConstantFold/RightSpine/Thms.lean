module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.RightSpine.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.RightSpine.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.RightSpine

open Diamond (Ty Val ValueSort dataPorts)
open GVN.Elimination (Rewrite Routing splitOrigin)
open SubZero (model wordPort)
open RVSDG (Tuple)

variable {args : List (Ty Unit)} {past : List (List (Ty Unit))}
variable {known : Prefix args past} {lhs rhs : WordWire args past} {edit : AddRewrite.Splice args past}

/-- The newest add fact records the two actual operand wires, in order. -/
theorem Prefix.record_addends (known : Prefix args past) (lhs rhs : WordWire args past)
    (wire : WordWire args (past ++ [[wordPort]])) (latest : splitOrigin [wordPort] wire = .inr .head) :
    (known.record .add (.cons lhs (.cons rhs .nil))).addends wire = some (Addends.mk lhs rhs).weaken := by
  simp only [Prefix.record, Prefix.extendAddends, latest, Option.map]

/-- An accepted rotation uses two distinct, nonliteral add wires and
uses the recorded right addition's operands in their source order. -/
theorem match_exact (accepted : matchAdd? known lhs rhs = some edit) :
    (known.literals lhs).isNone = true ∧ (known.literals rhs).isNone = true ∧ lhs.address ≠ rhs.address ∧
      ∃ left right, known.addends lhs = some left ∧ known.addends rhs = some right ∧
        edit = rotate lhs right :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.RightSpine.match_exact accepted

variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}
variable {program : Program SubZero.Opcode inputs out}
variable {rewrite : Rewrite SubZero.Opcode (dataPorts inputs) [] program.sigs}

/-- Every original wire reads the same value after routing. The fresh
inner sum is an additional intermediate. -/
theorem step_agrees (accepted : step? program = some rewrite)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    Routing.Agrees rewrite.route model entry (program.dataflow.eval model entry PUnit.unit)
      (rewrite.flow.eval model entry PUnit.unit) :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.RightSpine.step_agrees accepted entry

/-- The routed return agrees for every typed input in the word model. -/
theorem step_eval_eq (accepted : step? program = some rewrite)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    (AddRewrite.rewrittenProgram program rewrite).eval model entry = program.eval model entry :=
  (step_agrees accepted entry _ program.result).symm

end Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.RightSpine
