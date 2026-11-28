module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Worklist.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Worklist.Correctness

/-! Exact equations, FIFO drainage, and agreement with the simultaneous assignment. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Worklist

open SeaOfNodes.Diamond (Model Signature ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open SeaOfNodes.Loop.SCCP.Worklist.Split (Task)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {m : Model.{u, v, w} Op}
variable [BankDecidableEq m.value (dataPorts regs)]
variable {p : Program Op regs out} {input : Tuple (Fact m.value) (dataPorts regs)}

theorem evaluate_eq (job : Task regs) (state : State m.value regs out) :
    evaluate m p input job (dependencies state job) = get (transfer m p input state) job :=
  Proofs.evaluate_eq job state

theorem mem_wake_iff (old new : State m.value regs out) (pending : List (Task regs)) (job : Task regs) :
    job ∈ wake old new pending ↔
      job ∈ pending ∨ dependencies new job ≠ dependencies old job :=
  Proofs.mem_wake_iff old new pending job

theorem step_nodup (job : Task regs) (state : State m.value regs out) {pending : List (Task regs)}
    (nodup : pending.Nodup) : (step m p input job state pending).2.Nodup :=
  Proofs.step_nodup job state nodup

theorem step_decreases (job : Task regs) (state : State m.value regs out) (pending : List (Task regs))
    (ascending : state ≤ transfer m p input state) :
    potential (step m p input job state pending).1 (step m p input job state pending).2 <
      potential state (job :: pending) :=
  Proofs.step_decreases job state pending ascending

theorem run_drains (m : Model.{u, v, w} Op) [BankDecidableEq m.value (dataPorts regs)]
    (p : Program Op regs out) (input : Tuple (Fact m.value) (dataPorts regs)) :
    (run m p input).pending = [] :=
  (Proofs.run_spec (m := m) (p := p) (input := input)).1

/-- The entire drained assignment agrees, including all four occurrence
marks, every typed Φ destination, and the return fact. -/
theorem solve_eq_simultaneous (m : Model.{u, v, w} Op) [BankDecidableEq m.value (dataPorts regs)]
    (p : Program Op regs out) (input : Tuple (Fact m.value) (dataPorts regs)) :
    solve m p input = SCCP.solve m p input :=
  (Proofs.run_spec (m := m) (p := p) (input := input)).2

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Worklist
