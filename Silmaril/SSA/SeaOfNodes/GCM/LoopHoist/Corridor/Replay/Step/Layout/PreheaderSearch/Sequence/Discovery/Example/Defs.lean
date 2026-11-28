module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Example.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Example.Defs

/-! # The live-inventory scan finds a newly available consumer after a hoist -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery.Example

open Silmaril.MLIR.Arith (Width)
open CrossBlock.Example (packets runs)
open PreheaderSearch.Example (branchPackets)
open Layout.Example (seed?)

variable {Input : List Width} {saved carried result : Width}

def traceCuts {source : Layout.Output Input saved carried result} {requests : List Sequence.Request} :
    Sequence.Trace source requests → List Nat
  | .done => []
  | .step first tail => first.ranked.selection.1.cut :: traceCuts tail

def firstOutput? {source : Layout.Output Input saved carried result} {requests : List Sequence.Request} :
    Sequence.Trace source requests → Option (Layout.Output Input saved carried result)
  | .done => none
  | .step first _ => some first.ranked.selection.2

def admittedOrigins (source : Layout.Output Input saved carried result) : List Nat :=
  source.2.reference.origins.filter fun origin => (hoist? source origin).isSome

structure Observation where
  initialCandidates : List Nat
  afterFirstCandidates : List Nat
  consumerCuts : List Nat × List Nat
  requests : List Nat
  physicalCuts : List Nat
  terminalOrigins : List Nat
  fixedPoint : Bool
  beforeEdges : List (Nat × List Nat)
  afterEdges : List (Nat × List Nat)
  beforePackets : List (List Nat)
  afterPackets : List (List Nat)
  beforeRuns : List (Option Nat)
  afterRuns : List (Option Nat)
  deriving BEq, Repr

/-- Origin 6 becomes eligible when origin 5 is saved. Origin 7 then uses
    both saves. All three requests come from the live-inventory scan. -/
def observe : Option Observation := do
  let ⟨_, _, state⟩ ← seed?
  let source : Layout.Output _ _ _ _ := ⟨_, state⟩
  let plan ← schedule? source
  let middle ← firstOutput? plan.trace
  let final := plan.output
  let beforeEdges ← branchPackets state.cfg
  let afterEdges ← branchPackets final.2.cfg
  let beforePackets ← packets state.cfg
  let afterPackets ← packets final.2.cfg
  pure ⟨admittedOrigins source, admittedOrigins middle,
    (Layout.Discovery.acceptedCuts state 6, Layout.Discovery.acceptedCuts middle.2 6),
    plan.requests.map Sequence.Request.origin, traceCuts plan.trace, final.2.reference.origins,
    (choose? final).isNone, beforeEdges, afterEdges, beforePackets, afterPackets, runs state.cfg, runs final.2.cfg⟩

/-- A validated fixed point yields an empty schedule. A mismatched inventory is refused. -/
def stopCases : Option (Bool × Bool) := do
  let ⟨_, _, state⟩ ← seed?
  let plan ← schedule? ⟨_, state⟩
  let empty ← schedule? plan.output
  let invalid := { state with reference := { state.reference with origins := [] } }
  pure (empty.requests.isEmpty, (schedule? ⟨_, invalid⟩).isNone)

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery.Example
