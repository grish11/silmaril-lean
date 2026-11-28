module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Correctness
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Thms

/-! Termination and exact agreement of the mixed FIFO and simultaneous solver. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split

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

/-- The mixed FIFO uses the same typed update as the standalone Φ scheduler. -/
theorem phi_update_eq (dst : Phi.Job carried) (state : State m.value carried out) :
    update m g input (.phi dst) state = Phi.update m g input dst state := rfl

theorem mem_wake_iff (old new : State m.value carried out) (pending : List (Task carried)) (job : Task carried) :
    job ∈ wake m g input old new pending ↔
      job ∈ pending ∨ dependencies m g input new job ≠ dependencies m g input old job :=
  Proofs.mem_wake_iff old new pending job

theorem step_nodup (job : Task carried) (state : State m.value carried out) {pending : List (Task carried)}
    (nodup : pending.Nodup) : (step m g input job state pending).2.Nodup :=
  Proofs.step_nodup job state nodup

theorem step_stable (job : Task carried) (state : State m.value carried out) (pending : List (Task carried))
    (stable : Stable m g input state (job :: pending)) :
    Stable m g input (step m g input job state pending).1 (step m g input job state pending).2 :=
  Proofs.stable_step job state pending stable

theorem step_decreases (job : Task carried) (state : State m.value carried out) (pending : List (Task carried))
    (ascending : state ≤ SCCP.transfer m g input state) :
    potential (step m g input job state pending).1 (step m g input job state pending).2 <
      potential state (job :: pending) :=
  Proofs.step_decreases job state pending ascending

/-- A different notifier can reuse the FIFO convergence proof. Unqueued
equations must retain their right-hand sides across the pop. -/
theorem run_with_wake
    (notify : Task carried → State m.value carried out → State m.value carried out →
      List (Task carried) → List (Task carried))
    (quiet : ∀ job state pending reader,
      let new := update m g input job state
      reader ∉ notify job state new pending → reader ∉ pending ∧
        get (SCCP.transfer m g input new) reader = get (SCCP.transfer m g input state) reader)
    (bounded : ∀ job state new pending,
      (notify job state new pending).length ≤ pending.length + (dataPorts carried).length.succ.succ)
    (unchanged : ∀ job state pending, notify job state state pending = pending) :
    let result := FIFO.runSteps (fun job state pending =>
      let new := update m g input job state
      (new, notify job state new pending)) (potential (⊥ : State m.value carried out) initial) ⊥ initial
    result.pending = [] ∧ result.state = SCCP.solve m g input :=
  Proofs.run_with_wake notify quiet bounded unchanged

attribute [local irreducible] run solve SCCP.solve

/-- The potential bounds the number of pops from the initial assignment. -/
theorem run_drains : (run m g input).pending = [] :=
  (Proofs.run_spec (m := m) (g := g) (input := input)).1

/-- The full assignment agrees, including marks, every Φ coordinate and the exit fact. -/
theorem solve_eq_simultaneous : solve m g input = SCCP.solve m g input :=
  (Proofs.run_spec (m := m) (g := g) (input := input)).2

theorem solve_eq_worklist : solve m g input = Worklist.solve m g input :=
  (solve_eq_simultaneous m g input).trans (Worklist.solve_eq_simultaneous m g input).symm

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split
