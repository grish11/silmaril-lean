module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize

open Diamond (Val ValueSort dataPorts)
open GVN (Producer)
open GVN.Elimination (Routing)
open LeftSpine (SourceIds)
open SubZero (model word)
open RVSDG (Tuple)

variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}
variable {ids : SourceIds} {program : Program SubZero.Opcode inputs out}
variable {candidate : Producer program.dataflow word} {applied : Applied (dataPorts inputs) [] program.sigs}

/-- All original reads agree under the routed rewrite of the nominated add. -/
theorem step_agrees (accepted : step ids program candidate = .ok (some applied))
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    Routing.Agrees applied.rewrite.route model entry (program.dataflow.eval model entry PUnit.unit)
      (applied.rewrite.flow.eval model entry PUnit.unit) :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.step_agrees accepted entry

/-- The routed return agrees for all typed word inputs. -/
theorem step_eval_eq (accepted : step ids program candidate = .ok (some applied))
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    (AddRewrite.rewrittenProgram program applied.rewrite).eval model entry = program.eval model entry :=
  (step_agrees accepted entry _ program.result).symm

end Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize
