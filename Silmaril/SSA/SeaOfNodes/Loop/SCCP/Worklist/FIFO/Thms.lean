module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.FIFO.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.Worklist.FIFO.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.FIFO

open Semantics.Dataflow.FiniteHeight (HeightBound)

variable {State Job : Type*}

theorem mem_wake_iff [DecidableEq Job] (jobs : List Job) (changed : Job → Bool) (pending : List Job) (job : Job) :
    job ∈ wake jobs changed pending ↔ job ∈ pending ∨ (job ∈ jobs ∧ changed job = true) :=
  Proofs.mem_wake_iff jobs changed pending job

theorem wake_nodup [DecidableEq Job] {jobs pending : List Job} (changed : Job → Bool)
    (enumerated : jobs.Nodup) (nodup : pending.Nodup) : (wake jobs changed pending).Nodup :=
  Proofs.wake_nodup changed enumerated nodup

theorem potential_decreases [PartialOrder State] (height : HeightBound State) (jobs : Nat)
    {state new : State} {job : Job} {pending next : List Job}
    (ascending : state ≤ new) (size : next.length ≤ pending.length + jobs)
    (unchanged : new = state → next = pending) :
    potential height jobs new next < potential height jobs state (job :: pending) :=
  Proofs.potential_decreases height jobs ascending size unchanged

variable [PartialOrder State]
variable {transfer : State → State} {step : Job → State → List Job → State × List Job}
variable {stable : State → List Job → Prop} {measure : State → List Job → Nat}

theorem runSteps_checked
    (transfer_mono : Monotone transfer)
    (le_update : ∀ job state pending, state ≤ transfer state → state ≤ (step job state pending).1)
    (update_le : ∀ job state pending upper, state ≤ upper → transfer state ≤ upper → (step job state pending).1 ≤ upper)
    (stable_step : ∀ job state pending, stable state (job :: pending) →
      stable (step job state pending).1 (step job state pending).2)
    (decreases : ∀ job state pending, state ≤ transfer state →
      measure (step job state pending).1 (step job state pending).2 < measure state (job :: pending))
    (positive : ∀ job state pending, 0 < measure state (job :: pending))
    (fuel : Nat) (state upper : State) (pending : List Job)
    (fixed : transfer upper = upper) (ascending : state ≤ transfer state)
    (below : state ≤ upper) (invariant : stable state pending) (budget : measure state pending ≤ fuel) :
    let result := runSteps step fuel state pending
    result.pending = [] ∧ result.state ≤ upper ∧ stable result.state result.pending :=
  Proofs.runSteps_checked transfer_mono le_update update_le stable_step decreases positive
    fuel state upper pending fixed ascending below invariant budget

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.FIFO
