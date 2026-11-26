module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index.Correctness
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Thms

/-! The indexed notifier and the roster scan produce the same FIFO. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index

open Diamond (Model Signature Ty ValueSort dataPorts)
open Diamond.SCCP (Fact)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out : ValueSort Data} {g : Graph Op inputs carried entrySigs headerSigs out}
variable {m : Model.{u, v, w} Op} [BankDecidableEq m.value (dataPorts carried)]
variable {input : Tuple (Fact m.value) (dataPorts inputs)}
variable (index : Index g)

/-- The reverse lookup reports exactly the Φ jobs with changed watches, before
excluding jobs already pending. -/
theorem mem_destinations_iff (old new : State m.value carried out) (dst : Phi.Job carried) :
    dst ∈ index.destinations old new ↔ Phi.dependencies m g input new dst ≠ Phi.dependencies m g input old dst :=
  Proofs.mem_destinations_iff index old new dst

/-- Queue equality preserves the pending prefix and the order of every new job. -/
theorem wake_eq (old new : State m.value carried out) (pending : List (Task carried)) :
    wake m index old new pending = Split.wake m g input old new pending :=
  Proofs.wake_eq index old new pending

/-- Indexed notification leaves the update and its ordered wake unchanged. -/
theorem step_eq (job : Task carried) (state : State m.value carried out) (pending : List (Task carried)) :
    step m input index job state pending = Split.step m g input job state pending :=
  Proofs.step_eq index job state pending

/-- Comparing a pop's typed write decides whether its whole bank changed. -/
theorem bankChangedAfter_iff (job : Task carried) (state : State m.value carried out) :
    let new := Split.update m g input job state
    bankChangedAfter job state new = true ↔ new.2.1 ≠ state.2.1 :=
  Proofs.bankChangedAfter_iff (m := m) (g := g) (input := input) job state

/-- Entry and exit marks and the exact bank change reproduce both reference watches. -/
theorem gatedWatchesAfter_eq (job : Task carried) (state : State m.value carried out) :
    let new := Split.update m g input job state
    let changed := bankChangedAfter job state new
    gatedBankChanged (incomingIndex .entry) state.1 new.1 changed =
        decide (Worklist.dependencies new .control ≠ Worklist.dependencies state .control) ∧
      gatedBankChanged exitIndex state.1 new.1 changed =
        decide (Worklist.dependencies new .result ≠ Worklist.dependencies state .result) :=
  Proofs.gatedWatchesAfter_eq (m := m) (g := g) (input := input) job state

/-- One popped job has enough information to recover the general Φ notifications. -/
theorem destinationsAfter_eq (job : Task carried) (state : State m.value carried out) :
    let new := Split.update m g input job state
    index.destinationsAfter job state new = index.destinations state new :=
  Proofs.destinationsAfter_eq (m := m) (input := input) index job state

/-- The specialized pop has the same full assignment and ordered pending queue
as the general indexed step. -/
theorem stepLocal_eq (job : Task carried) (state : State m.value carried out) (pending : List (Task carried)) :
    stepLocal m input index job state pending = step m input index job state pending :=
  Proofs.stepLocal_eq index job state pending

/-- The specialized runner agrees at every budget, including the visit trace. -/
theorem runSteps_eq_step : runSteps m input index = FIFO.runSteps (step m input index) :=
  Proofs.runSteps_eq_step index

theorem runSteps_eq : runSteps m input index = Split.runSteps m g input :=
  Proofs.runSteps_eq index

/-- The same budget gives the same state, pending queue, and visit trace. -/
theorem run_eq : run m input index = Split.run m g input :=
  congrFun (congrFun (congrFun (runSteps_eq index) _) _) _

theorem run_drains : (run m input index).pending = [] :=
  (congrArg FIFO.Run.pending (run_eq index)).trans (Split.run_drains m g input)

/-- All edge marks, typed Φ facts, and the result fact agree with the simultaneous solution. -/
theorem solve_eq_simultaneous : solve m input index = SCCP.solve m g input :=
  (congrArg FIFO.Run.state (run_eq index)).trans (Split.solve_eq_simultaneous m g input)

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index
