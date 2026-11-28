module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.OperandWatches.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Support.Example.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Example.Defs

/-! Compare whole-bank and operand-support wakes on existing Boolean/byte loops. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.OperandWatches.Example

open SCCP.Example (word)
open SCCP.Example.Bank (fields model facts observe)
open Phi.Support.Example (graph before)
open Semantics.Dataflow (Flat)

def watches := build (Index.build graph)

def bothWatchesActive : State model.value fields word := (insert exitIndex before.1, before.2)

/-- Both watches are active. The guard reads a capture and the result reads
the byte, so neither reads the written carried flag. -/
def skippedFlag : List (Job 2) × List (Job 2) :=
  let old := Phi.write bothWatchesActive (0 : Fin 2) .bottom
  let job : Job 2 := .phi 0
  ((Index.stepLocal model (facts true 255) watches.index job old []).2,
    (step model (facts true 255) watches job old []).2)

/-- Publishing the byte wakes its Φ readers and the active result watch. -/
def resultReadsByte : List (Job 2) :=
  let old := Phi.write bothWatchesActive (1 : Fin 2) .bottom
  (step model (facts true 255) watches (.phi (1 : Fin 2)) old []).2

/-- In the other fixture, the guard reads the byte through the update producer. -/
def guardReadsByte : List (Job 2) :=
  let guarded := build (Index.build (SCCP.Example.Bank.graph false))
  (step model (facts true 0) guarded (.phi (1 : Fin 2)) Phi.Example.beforeWidening []).2

/-- Activating exit without a bank write still appends result behind a pending Φ. -/
def exitActivation : List (Job 2) :=
  let old : State model.value fields word := (before.1.erase (incomingIndex .backedge), before.2)
  (step model (facts false 255) watches .control old [.phi (1 : Fin 2)]).2

def solveReport : List (Job 2) × Bool × Bool × (Flat Bool × Flat Nat) × Flat Nat :=
  let done := run model (facts true 255) watches
  (done.pending, decide (incomingIndex .backedge ∈ done.state.1), decide (exitIndex ∈ done.state.1),
    observe done.state.2.1, done.state.2.2.map BitVec.toNat)

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.OperandWatches.Example
