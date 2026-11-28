module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddChain.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddChain.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddChain

open Diamond (Ty Val ValueSort dataPorts)
open GVN.Elimination (Rewrite Routing)
open SubZero (model)
open RVSDG (Locals Tuple Wires)

variable {args : List (Ty Unit)} {past : List (List (Ty Unit))}
variable {known : Prefix args past} {entry : Tuple (Val model.value) args}
variable {locals : Locals (Val model.value) past}

/-- The explicit-literal analysis starts with an empty prefix. -/
theorem Prefix.empty_agrees (entry : Tuple (Val model.value) args) :
    (Prefix.empty (args := args)).Agrees entry PUnit.unit :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddChain.empty_agrees entry

/-- Recording a binding keeps the explicit-literal and offset facts sound. -/
theorem Prefix.record_agrees (agree : known.Agrees entry locals) {ins : List (ValueSort Unit)} {out : ValueSort Unit}
    (op : SubZero.Opcode ins out) (operands : Wires args past (dataPorts ins)) :
    (known.record op operands).Agrees entry
      (locals.snoc (.cons (model.run op (operands.read entry locals)) .nil)) :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddChain.record_agrees agree op operands

/-- The accepted chain splice has the original add's value in this prefix. -/
theorem match_agrees {lhs rhs : WordWire args past} {edit : AddRewrite.Splice args past}
    (agree : known.Agrees entry locals) (accepted : rules.matchAdd? known lhs rhs = some edit) :
    AddRewrite.evalAdd lhs rhs entry locals = edit.eval entry locals :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddChain.match_agrees agree accepted

variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}
variable {program : Program SubZero.Opcode inputs out}
variable {rewrite : Rewrite SubZero.Opcode (dataPorts inputs) [] program.sigs}

/-- All original typed producer and argument reads agree under the
routing returned by a successful step. -/
theorem step_agrees (accepted : step? program = some rewrite)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    Routing.Agrees rewrite.route model entry (program.dataflow.eval model entry PUnit.unit)
      (rewrite.flow.eval model entry PUnit.unit) :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddChain.step_agrees accepted entry

/-- Using the routed result preserves the native return at every input. -/
theorem step_eval_eq (accepted : step? program = some rewrite)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    (rewrittenProgram program rewrite).eval model entry = program.eval model entry :=
  (step_agrees accepted entry _ program.result).symm

end Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddChain
