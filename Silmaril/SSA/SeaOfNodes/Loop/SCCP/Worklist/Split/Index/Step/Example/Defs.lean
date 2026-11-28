module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Support.Example.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index.Defs

/-! Pop one job from the indexed FIFO on the transitive Boolean/byte fixture. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index.Step.Example

open SCCP.Example (word)
open SCCP.Example.Bank (fields model facts observe)
open Phi.Support.Example (graph before)
open Semantics.Dataflow (Flat)

def index := Index.build graph

/-- Report the feedback mark, both carried facts, the pending queue and the visits. -/
def popReport (job : Job 2) (state : State model.value fields word) (pending : List (Job 2)) :
    Bool × (Flat Bool × Flat Nat) × List (Job 2) × List (Job 2) :=
  let run := Index.runSteps model (facts true 255) index 1 state (job :: pending)
  (decide (incomingIndex .backedge ∈ run.state.1), observe run.state.2.1, run.pending, run.visits)

def noOp := popReport (.phi 1) before [.result]

def transitiveWake := popReport (.phi 1) (Phi.write before (1 : Fin 2) .bottom) []

def feedbackActivation :=
  popReport .control (before.1.erase (incomingIndex .backedge), before.2) [.phi 1]

/-- An active control watch still sees the byte changed by Φ even though
the guard reads a capture. An active result watch sees the same change. -/
def activeWatches :=
  popReport (.phi 1) (Phi.write (insert exitIndex before.1, before.2) (1 : Fin 2) .bottom) []

/-- With entry disabled, a flag write only wakes the active result watch.
That watch sees the flag even though the result wire reads the byte. -/
def exitOnlyWatch :=
  let marks := insert exitIndex (before.1.erase (incomingIndex .entry))
  popReport (.phi 0) (Phi.write (marks, before.2) (0 : Fin 2) .bottom) []

/-- The control pop marks exit without a carried write and queues the result. -/
def exitActivation : Bool × (Flat Bool × Flat Nat) × List (Job 2) × List (Job 2) :=
  let old : State model.value fields word := (before.1.erase (incomingIndex .backedge), before.2)
  let run := Index.runSteps model (facts false 255) index 1 old [.control, .phi (1 : Fin 2)]
  (decide (exitIndex ∈ run.state.1), observe run.state.2.1, run.pending, run.visits)

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index.Step.Example
