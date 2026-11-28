module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.OperandWatches.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.OperandWatches.Correctness

/-! Support-based notifications converge to the simultaneous SCCP assignment. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.OperandWatches

open Diamond (Model Signature Ty ValueSort dataPorts)
open Diamond.SCCP (Fact)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out : ValueSort Data} {g : Graph Op inputs carried entrySigs headerSigs out}
variable {m : Model.{u, v, w} Op} [BankDecidableEq m.value (dataPorts carried)]
variable {input : Tuple (Fact m.value) (dataPorts inputs)}
variable (watches : OperandWatches g)

/-- A quiet control watch leaves the control equation unchanged across the pop. -/
theorem control_eq_of_quiet (job : Task carried)
    (state new : State m.value carried out) (updated : new = Split.update m g input job state)
    (quiet : watches.candidateChanged job state.1 new.1 (Index.bankChangedAfter job state new) .control = false) :
    Split.get (SCCP.transfer m g input new) .control = Split.get (SCCP.transfer m g input state) .control :=
  Proofs.control_eq_of_quiet watches job state new updated quiet

/-- A quiet result watch leaves the gated result equation unchanged across the pop. -/
theorem result_eq_of_quiet (job : Task carried)
    (state new : State m.value carried out) (updated : new = Split.update m g input job state)
    (quiet : watches.candidateChanged job state.1 new.1 (Index.bankChangedAfter job state new) .result = false) :
    Split.get (SCCP.transfer m g input new) .result = Split.get (SCCP.transfer m g input state) .result :=
  Proofs.result_eq_of_quiet watches job state new updated quiet

/-- The existing finite-height budget drains the refined FIFO from bottom. -/
theorem run_drains : (run m input watches).pending = [] := (Proofs.run_spec watches).1

/-- The drained result agrees on all marks, carried fields and the result fact. -/
theorem solve_eq_simultaneous : solve m input watches = SCCP.solve m g input := (Proofs.run_spec watches).2

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.OperandWatches
