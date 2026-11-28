module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Replay.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Replay.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Replay

open Diamond (Val ValueSort dataPorts)
open GVN (Producer)
open GVN.Elimination (Routing)
open LeftSpine (SourceIds)
open RightSpine (WordWire)
open SubZero (model word)
open RVSDG (Tuple extend)

variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}
variable {program : Program SubZero.Opcode inputs out} {candidate : Producer program.dataflow word}

/-- A successful lookup identifies the exact typed wire in the current table. -/
theorem findProducer?_exact {wire : WordWire (dataPorts inputs) (extend [] program.sigs)}
    (found : findProducer? program wire = some candidate) : candidate.origin = wire :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Replay.find_exact found

/-- The composed map preserves every original typed read at every input,
including after a refusal or budget stop. -/
theorem run_agrees (fuel : Nat) (ids : SourceIds) (program : Program SubZero.Opcode inputs out)
    (candidate : Producer program.dataflow word) (entry : Tuple (Val model.value) (dataPorts inputs)) :
    let result := run fuel ids program candidate
    Routing.Agrees result.rewrite.route model entry (program.dataflow.eval model entry PUnit.unit)
      (result.rewrite.flow.eval model entry PUnit.unit) :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Replay.run_agrees fuel ids program candidate entry

/-- Routing the return through the replay preserves its native value. -/
theorem run_eval_eq (fuel : Nat) (ids : SourceIds) (program : Program SubZero.Opcode inputs out)
    (candidate : Producer program.dataflow word) (entry : Tuple (Val model.value) (dataPorts inputs)) :
    (AddRewrite.rewrittenProgram program (run fuel ids program candidate).rewrite).eval model entry =
      program.eval model entry :=
  (run_agrees fuel ids program candidate entry _ program.result).symm

/-- The trace contains at most one accepted edit per unit of fuel. -/
theorem run_rules_le (fuel : Nat) (ids : SourceIds) (program : Program SubZero.Opcode inputs out)
    (candidate : Producer program.dataflow word) : (run fuel ids program candidate).rules.length ≤ fuel :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Replay.run_rules_le fuel ids program candidate

end Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Replay
