module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.Example.Defs

/-! # Two admitted physical cuts compete with the actual header walk -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Example

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg Terminator)
open Corridor.Example (Inputs word input)
open Loop.MLIR.CF (TargetOp evalOp)
open CrossBlock.Example (packets runs)
open HeaderSplice.Walk.Example (start?)
open Step.Example (words)

def branchPackets {saved : Width} {extra : List Width}
    (cfg : Cfg TargetOp (Label saved word word extra) Inputs [word]) : Option (List (Nat × List Nat)) := do
  let inputs := input 2 10 1
  let .inl ⟨.header, args⟩ := cfg.entry.eval evalOp (fun term env => Terminator.eval env term) inputs | none
  pure $ ((cfg.block .header).eval evalOp Header.Typed.edgePackets (args.append inputs)).map fun (slot, frame) =>
    ((match slot with | .jump => 0 | .onTrue => 1 | .onFalse => 2), words frame.args)

structure Observation where
  physicalCuts : List Nat
  refusedZero : Bool
  visitedHeader : List Nat
  nominatedPoint : Nat × Nat
  selectedPoint : Nat × Nat
  depths : Nat × Nat
  earlierSlot : Option Nat
  latestSlot : Option Nat
  beforeEdges : List (Nat × List Nat)
  afterEdges : List (Nat × List Nat)
  beforePackets : List (List Nat)
  afterPackets : List (List Nat)
  beforeRuns : List (Option Nat)
  afterRuns : List (Option Nat)
  deriving BEq, Repr

/-- The same live origin reaches header index 3 in the old ranker when
    nominated at cut 0. The search instead emits the later physical cut. -/
def observe : Option Observation := do
  let ⟨_, _, state⟩ ← start?
  let nominated ← HeaderSplice.Walk.rank? state ⟨5, 0⟩ 4
  let ranked ← rank? state 5 4
  let earlier ← Layout.emit? state ⟨5, 1⟩
  let (_, newMove) ← latest? state 5
  let target := ranked.selection.2.2.cfg
  let beforeEdges ← branchPackets state.cfg
  let afterEdges ← branchPackets target
  let beforePackets ← packets state.cfg
  let afterPackets ← packets target
  let point := fun (p : Point _) => (CrossBlock.blockNumber p.block, p.cut)
  let control := ranked.crossBlock.control
  pure ⟨Layout.Discovery.acceptedCuts state 5, nominated.crossBlock.preheader.isNone,
    ranked.walked.trace.positions.map HeaderSplice.Walk.Position.index,
    point nominated.selection.1, point ranked.selection.1,
    (control.depth none, control.depth nominated.selection.1.block),
    earlier.next.physicalSlot? 5, newMove.next.physicalSlot? 5,
    beforeEdges, afterEdges, beforePackets, afterPackets, runs state.cfg, runs target⟩

/-- A cut beyond the saved prefix is invalid. Origin zero reads the latch,
    so the preheader search refuses every cut and ranking stays in the header. -/
def refused : Option (Bool × Bool × Bool × Nat) := do
  let ⟨_, _, state⟩ ← start?
  let ranked ← rank? state 0 4
  let chosen := CrossBlock.blockNumber ranked.selection.1.block
  let readsLocal := ranked.walked.start.binding.sites.operands.any (fun point =>
    CrossBlock.blockNumber point.block == 1)
  pure ((Layout.emit? state ⟨5, state.savedCount + 1⟩).isNone, readsLocal,
    (latest? state 0).isNone, chosen)

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Example
