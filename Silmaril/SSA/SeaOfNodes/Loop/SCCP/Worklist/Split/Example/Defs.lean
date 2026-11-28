module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Example.Defs

/-! Run the mixed FIFO on the existing Boolean/byte carried bank. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Example

open SCCP.Example (Byte word)
open SCCP.Example.Bank (fields HeaderSigs Op model graph facts observe)
open Semantics.Dataflow (Flat)

/-- Both feedback destinations forward their own old typed field. -/
def direct : Graph Op fields fields [] HeaderSigs word :=
  { graph false with
    phiInputs
      | .entry => (graph false).phiInputs .entry
      | .backedge => .cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail (.tail (.tail .head)))) .nil) }

/-- Read the actual FIFO visit order, followed by the final marks and facts. -/
def report (program : Graph Op fields fields [] HeaderSigs word) (enabled : Bool) (start : Byte) :
    List (Job 2) × Bool × Bool × (Flat Bool × Flat Nat) × Flat Nat :=
  let result := run model program (facts enabled start)
  (result.visits, decide (incomingIndex .backedge ∈ result.state.1), decide (exitIndex ∈ result.state.1),
    observe result.state.2.1, result.state.2.2.map BitVec.toNat)

/-- One widening pop with feedback enabled and exit disabled. -/
def wideningWake (pending : List (Job 2)) : List (Job 2) :=
  (step model (graph false) (facts true 0) (.phi (1 : Fin 2)) Phi.Example.beforeWidening pending).2

/-- Observe which jobs are woken when only exit becomes enabled. -/
def enableExitWake : List (Job 2) :=
  let old := Phi.Example.beforeWidening
  let new : State model.value fields word := (insert exitIndex old.1, old.2)
  wake model (graph false) (facts true 0) old new []

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Example
