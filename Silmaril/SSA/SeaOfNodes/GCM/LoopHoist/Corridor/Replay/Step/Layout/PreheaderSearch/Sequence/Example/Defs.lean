module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Example.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Example.Defs

/-! # A producer move admits the dependent consumer on the emitted layout -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Example

open Silmaril.MLIR.Arith (Width)
open CrossBlock.Example (packets runs)
open PreheaderSearch.Example (branchPackets)
open Layout.Example (seed?)

def pointCoordinates {saved carried result : Width} {extra : List Width}
    (point : Point (Label saved carried result extra)) : Nat × Nat :=
  (CrossBlock.blockNumber point.block, point.cut)

structure Observation where
  beforeConsumerCuts : List Nat
  afterConsumerCuts : List Nat
  consumerOperandCuts : List (Nat × Nat)
  selections : List (Nat × Nat)
  consumerIndices : Nat × Nat
  savedCounts : List Nat
  physicalSlots : List (Option Nat)
  beforeEdges : List (Nat × List Nat)
  afterEdges : List (Nat × List Nat)
  beforePackets : List (List Nat)
  afterPackets : List (List Nat)
  beforeRuns : List (Option Nat)
  afterRuns : List (Option Nat)
  deriving BEq, Repr

/-- Origin 6 reads origin 5. Its live read becomes a physical preheader
    definition only after the first checked rank emits that producer. -/
def observe : Option Observation := do
  let ⟨_, _, state⟩ ← seed?
  let .ok trace@(.step producer (.step consumer .done)) := run ⟨_, state⟩ 0 [⟨5, 3⟩, ⟨6, 3⟩] | none
  let beforeConsumer ← CrossBlock.keep? state 6
  let current := producer.ranked.selection.2.2
  let final := trace.output.2
  let beforeEdges ← branchPackets state.cfg
  let afterEdges ← branchPackets final.cfg
  let beforePackets ← packets state.cfg
  let afterPackets ← packets final.cfg
  let operands := consumer.ranked.walked.start.binding.sites.operands.map pointCoordinates
  pure ⟨Layout.Discovery.acceptedCuts state 6, Layout.Discovery.acceptedCuts current 6, operands,
    [pointCoordinates producer.ranked.selection.1, pointCoordinates consumer.ranked.selection.1],
    (beforeConsumer.index, consumer.ranked.walked.start.binding.index),
    [state.savedCount, current.savedCount, final.savedCount], [5, 6].map final.physicalSlot?,
    beforeEdges, afterEdges, beforePackets, afterPackets, runs state.cfg, runs final.cfg⟩

structure MixedObservation where
  headerOrder : List Nat
  selections : List (Nat × Nat)
  secondIndex : Nat
  finalRuns : List (Option Nat)
  deriving BEq, Repr

/-- The latch-dependent origin 4 moves within the header. Origin 5 is
    then found at its new index and emitted into the preheader. -/
def mixed : Option MixedObservation := do
  let ⟨_, _, state⟩ ← seed?
  let .ok trace@(.step localMove (.step producer .done)) := run ⟨_, state⟩ 0 [⟨4, 3⟩, ⟨5, 3⟩] | none
  pure ⟨localMove.ranked.selection.2.2.reference.origins,
    [pointCoordinates localMove.ranked.selection.1, pointCoordinates producer.ranked.selection.1],
    producer.ranked.walked.start.binding.index, runs trace.output.2.cfg⟩

/-- Repeating the newly saved original identity refuses the next request. -/
def refused : Option Refusal := do
  let ⟨_, _, state⟩ ← seed?
  match run ⟨_, state⟩ 7 [⟨5, 3⟩, ⟨5, 3⟩] with
  | .error failure => some failure
  | .ok _ => none

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Example
