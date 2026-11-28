module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Replay.Defs
import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Equality.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Replay

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure
open Silmaril.SSA.SeaOfNodes.Pure.ConstantFold
open Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Replay
open Diamond (Val ValueSort dataPorts)
open GVN (Producer)
open GVN.Elimination (Routing)
open LeftSpine (SourceIds)
open RightSpine (WordWire)
open SubZero (model word wordPort)
open Silmaril.SSA.RVSDG (Tuple Wires extend)

variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}
variable {program : Program SubZero.Opcode inputs out}
variable {candidate : Producer program.dataflow word}

theorem find_exact {wire : WordWire (dataPorts inputs) (extend [] program.sigs)}
    (found : findProducer? program wire = some candidate) : candidate.origin = wire := by
  have tested := List.find?_some
    (p := fun ref : Producer program.dataflow word => decide (ref.origin.address = wire.address)) found
  have address : candidate.origin.address = wire.address := of_decide_eq_true tested
  have same := Silmaril.SSA.RVSDG.NestedTheta.Equality.addresses_injective
    (.cons candidate.origin .nil) (.cons wire .nil) (congrArg (fun a => [a]) address)
  exact congrArg (fun ws : Wires (dataPorts inputs) (extend [] program.sigs) [wordPort] => ws.get .head) same

theorem run_agrees (fuel : Nat) (ids : SourceIds) (program : Program SubZero.Opcode inputs out)
    (candidate : Producer program.dataflow word) (entry : Tuple (Val model.value) (dataPorts inputs)) :
    let result := run fuel ids program candidate
    Routing.Agrees result.rewrite.route model entry (program.dataflow.eval model entry PUnit.unit)
      (result.rewrite.flow.eval model entry PUnit.unit) := by
  induction fuel generalizing ids program with
  | zero => exact fun _ _ => rfl
  | succ fuel ih =>
    simp only [run]
    split
    · exact fun _ _ => rfl
    · exact fun _ _ => rfl
    · rename_i applied accepted
      have first := AddIdealize.step_agrees accepted entry
      dsimp only
      split
      · exact first
      · rename_i next found
        have tail := ih (idsAfter ids applied.rule) _ next
        intro t wire
        exact (first t wire).trans (tail t (applied.rewrite.route wire))

theorem run_rules_le (fuel : Nat) (ids : SourceIds) (program : Program SubZero.Opcode inputs out)
    (candidate : Producer program.dataflow word) : (run fuel ids program candidate).rules.length ≤ fuel := by
  induction fuel generalizing ids program with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
    simp only [run]
    split
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · rename_i applied _
      split
      · exact Nat.succ_le_succ (Nat.zero_le _)
      · rename_i next found
        exact Nat.succ_le_succ (ih (idsAfter ids applied.rule) _ next)

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Replay
