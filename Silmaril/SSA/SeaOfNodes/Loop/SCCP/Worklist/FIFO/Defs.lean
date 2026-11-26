module

public import Silmaril.Semantics.Dataflow.FiniteHeight.Defs

/-! Bounded FIFO execution shared by the carried-bank SCCP schedulers. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.FIFO

open Semantics.Dataflow.FiniteHeight (HeightBound)

variable {State Job : Type*}

structure Run (State Job : Type*) where
  state : State
  pending : List Job
  visits : List Job

def runSteps (step : Job → State → List Job → State × List Job) : Nat → State → List Job → Run State Job
  | _, state, [] => ⟨state, [], []⟩
  | 0, state, job :: pending => ⟨state, job :: pending, []⟩
  | budget + 1, state, job :: pending =>
    let next := step job state pending
    let rest := runSteps step budget next.1 next.2
    { rest with visits := job :: rest.visits }

/-- Keep the queue prefix, then add changed jobs in the supplied enumeration order. -/
def wake [DecidableEq Job] (jobs : List Job) (changed : Job → Bool) (pending : List Job) : List Job :=
  pending ++ jobs.filter (fun job => !pending.contains job && changed job)

def potential [PartialOrder State] (height : HeightBound State) (jobs : Nat)
    (state : State) (pending : List Job) : Nat :=
  (height.bound - height.rank state) * (jobs + 1) + pending.length

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.FIFO
