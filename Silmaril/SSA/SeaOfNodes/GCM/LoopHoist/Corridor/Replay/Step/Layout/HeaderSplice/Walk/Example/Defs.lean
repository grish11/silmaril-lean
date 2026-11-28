module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Example.Defs

/-! # Two checked crossings of one live binding on a lowered saved CFG -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.Example

open Silmaril.MLIR.Arith (Width)
open Corridor.Example (Inputs word)
open CrossBlock.Example (packets runs)
open HeaderSplice.Example (headerPackets)

/-- Start from the lowered two-save loop and place origin 5 before the
    two independent bindings using the existing checked emitter. -/
def start? : Option ((saved : Width) × (second : Width) × Layout.State Inputs saved word word [second]) := do
  let ⟨_, _, state⟩ ← CrossBlock.Example.seed?
  let first ← HeaderSplice.emit? state ⟨5, 2⟩
  let second ← HeaderSplice.emit? first.next ⟨5, 1⟩
  pure ⟨_, _, second.next⟩

structure Observation where
  indices : List Nat
  orders : List (List Nat)
  blocked : Bool
  blockedCut : Nat
  operandCuts : List (Nat × Nat)
  ordinaryReads : List Nat
  falseExitRead : Bool
  beforeEdges : List (Nat × List Nat)
  afterEdges : List (Nat × List Nat)
  beforePackets : List (List Nat)
  afterPackets : List (List Nat)
  beforeRuns : List (Option Nat)
  afterRuns : List (Option Nat)
  deriving BEq, Repr

def observe : Option Observation := do
  let ⟨_, _, state⟩ ← start?
  let walked ← walk? state 5 4
  let trace := walked.trace
  let final := trace.last.1.cfg
  let beforeEdges ← headerPackets state.cfg
  let afterEdges ← headerPackets final
  let beforePackets ← packets state.cfg
  let afterPackets ← packets final
  let uses := trace.last.2.binding.sites.uses
  let operands := trace.last.2.binding.sites.operands.map fun point => (CrossBlock.blockNumber point.block, point.cut)
  let ordinaryReads := uses.filterMap fun use =>
    match use with | .ordinary point => some point.cut | .phi .. => none
  let falseRead := uses.any fun use =>
    match use with | .phi (some ⟨_, .header⟩) .onFalse 0 => true | _ => false
  pure ⟨trace.positions.map Position.index, trace.positions.map (fun pos => pos.1.reference.origins),
    trace.blocked, trace.last.index + 2, operands, ordinaryReads, falseRead,
    beforeEdges, afterEdges, beforePackets, afterPackets, runs state.cfg, runs final⟩

def limited : Option (List Nat × Bool × Bool) := do
  let ⟨_, _, state⟩ ← start?
  let walked ← walk? state 5 1
  pure (walked.trace.positions.map Position.index, walked.trace.blocked, (walk? state 99 4).isNone)

def ranking : Option ((Nat × Nat) × (Nat × Nat) × (Nat × Nat) × List (Option Nat) × List (Option Nat)) := do
  let ⟨_, _, state⟩ ← start?
  let inside ← rank? state ⟨5, 0⟩ 4
  let outside ← rank? state ⟨5, 1⟩ 4
  let control := outside.crossBlock.control
  let point := fun (p : Point _) => (CrossBlock.blockNumber p.block, p.cut)
  pure ((control.depth none, control.depth inside.selection.1.block),
    point inside.selection.1, point outside.selection.1,
    runs inside.selection.2.2.cfg, runs outside.selection.2.2.cfg)

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.Example
