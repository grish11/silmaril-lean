module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Doubling.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Doubling.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Doubling

open Diamond (Ty Val ValueSort dataPorts)
open GVN.Elimination (Rewrite Routing)
open SubZero (model word wordPort)
open RVSDG (Locals Origin Tuple)

variable {args : List (Ty Unit)} {past : List (List (Ty Unit))}
variable {known : Literals args past} {lhs rhs : Origin args past wordPort}

/-- An accepted edit multiplies the exact common wire by two. -/
theorem match_exact {edit : AddRewrite.Edit args past} (accepted : matchAdd? known lhs rhs = some edit) :
    lhs = rhs ∧ edit = ⟨.mul, lhs, 2⟩ :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Doubling.match_exact accepted

/-- If the existing scan can fold this binding to a literal, doubling declines it. -/
theorem match_refuses_literal {literal : SubZero.Opcode [] word}
    (folded : binaryLiteral? known .add (.cons lhs (.cons rhs .nil)) = some literal) :
    matchAdd? known lhs rhs = none := by
  simp [matchAdd?, folded]

/-- The accepted doubling splice has the original add's value. -/
theorem match_agrees {entry : Tuple (Val model.value) args} {locals : Locals (Val model.value) past}
    {splice : AddRewrite.Splice args past} (agree : Scan.Literals.Agrees known entry locals)
    (accepted : rules.matchAdd? known lhs rhs = some splice) :
    AddRewrite.evalAdd lhs rhs entry locals = splice.eval entry locals :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Doubling.match_agrees agree accepted

variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}
variable {program : Program SubZero.Opcode inputs out}
variable {rewrite : Rewrite SubZero.Opcode (dataPorts inputs) [] program.sigs}

/-- A successful step preserves every original typed read through the routing. -/
theorem step_agrees (accepted : step? program = some rewrite)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    Routing.Agrees rewrite.route model entry (program.dataflow.eval model entry PUnit.unit)
      (rewrite.flow.eval model entry PUnit.unit) :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Doubling.step_agrees accepted entry

/-- The routed return agrees at every input in the modular word model. -/
theorem step_eval_eq (accepted : step? program = some rewrite)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    (AddRewrite.rewrittenProgram program rewrite).eval model entry = program.eval model entry :=
  (step_agrees accepted entry _ program.result).symm

end Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Doubling
