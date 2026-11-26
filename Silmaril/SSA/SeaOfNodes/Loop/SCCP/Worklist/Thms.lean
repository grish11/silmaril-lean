module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.Worklist.Correctness
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.Worklist.Equations

/-! Termination and exact agreement with the simultaneous loop solver. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist

open Diamond (Model Signature Ty ValueSort dataPorts)
open Diamond.SCCP (Fact)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out : ValueSort Data}
variable (m : Model.{u, v, w} Op) [BankDecidableEq m.value (dataPorts carried)]
variable (g : Graph Op inputs carried entrySigs headerSigs out)
variable (input : Tuple (Fact m.value) (dataPorts inputs))

/-- The watched inputs suffice to evaluate the corresponding transfer equation. -/
theorem evaluate_eq (job : Task) (state : State m.value carried out) :
    evaluate m g input job (dependencies state job) = get (SCCP.transfer m g input state) job :=
  Proofs.evaluate_eq job state

/-- A pop from an ascending assignment strictly decreases the queue potential. -/
theorem step_decreases (job : Task) (state : State m.value carried out) (pending : List Task)
    (ascending : state ≤ SCCP.transfer m g input state) :
    potential (step m g input job state pending).1 (step m g input job state pending).2 <
      potential state (job :: pending) :=
  Proofs.step_decreases job state pending ascending

theorem step_nodup (job : Task) (state : State m.value carried out) {pending : List Task}
    (nodup : pending.Nodup) : (step m g input job state pending).2.Nodup :=
  Proofs.step_nodup job state nodup

attribute [local irreducible] run solve SCCP.solve

/-- The certified budget always takes the queue to empty. -/
theorem run_drains : (run m g input).pending = [] :=
  (Proofs.run_spec (m := m) (g := g) (input := input)).1

/-- All control, bank, and result facts agree with the simultaneous least solution. -/
theorem solve_eq_simultaneous : solve m g input = SCCP.solve m g input :=
  (Proofs.run_spec (m := m) (g := g) (input := input)).2

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist
