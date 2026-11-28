module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Example.Defs

/-! # Sink three dependent bindings across two retained bindings -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Example

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Terminator)
open Loop.MLIR.CF (evalOp)
open Corridor.Example (input)
open Corridor.Header.Typed (edgePackets swapAt?)
open Corridor.Replay
open Corridor.AfterReorder.Second.Example (first)
open Corridor.Replay.Example (producer consumer)
open Corridor.Replay.Step.Example (words)
open Corridor.Replay.Step.Layout (initial?)
open Corridor.Replay.Step.Layout.Example (seed?)
open ExitSink.Example (feedbackLoop runs)

variable {Input extra : List Width} {saved carried result : Width}

/-- The checked input header starts in origin order [3, 5, 0, 6, 4, 7].
Origin 6 reads origin 5. Origin 4 supplies the unchanged feedback update. -/
def interleave? (source : Source Input saved carried result extra) :
    Option (Source Input saved carried result extra) := do
  let first ← swapAt? 2 (source.block .header)
  let second ← swapAt? 1 first
  let header ← swapAt? 3 second
  pure (withHeader source header)

def mask : List Bool := [false, true, false, true, false, true]

structure Observation where
  retained : List Nat
  moved : List Nat
  headerBindings : Nat
  exitBindings : Nat
  exitOperandCuts : List (List Nat)
  beforePackets : List (List Nat)
  afterPackets : List (List Nat)
  restoredPackets : List (List Nat)
  beforeRuns : List (Option Nat)
  afterRuns : List (Option Nat)
  deriving BEq, Repr

def observe : Option Observation := do
  let ⟨_, _, state⟩ ← seed?
  let source ← interleave? state.cfg
  let sunk ← sink? source mask
  let inputs := input 2 10 1
  let .inl ⟨.header, packet⟩ := source.entry.eval evalOp (fun term vals => Terminator.eval vals term) inputs | none
  let before := (source.block .header).eval evalOp edgePackets (packet.append inputs)
  let after := (sunk.cfg.block .header).eval evalOp edgePackets (packet.append inputs)
  let [test, step, feedback, producerId, consumerId, returned] := state.reference.origins | none
  let origins := [test, producerId, step, consumerId, feedback, returned]
  pure ⟨selected false mask origins, selected true mask origins,
    (shape sunk.cfg (some ⟨_, .header⟩)).bindings, (shape sunk.cfg exitId).bindings,
    (Suffix.sites exitId 0 (sunk.cfg.block .exit)).map (fun site => site.operands.map Point.cut),
    before.map (fun (_, frame) => words frame.args), after.map (fun (_, frame) => words frame.args),
    after.map (fun (_, frame) => words (sunk.sunk.restorePacket frame).args), runs source, runs sunk.cfg⟩

/-- Origin 6 is retained while its producer at index 1 is nominated.
The unsunk consumer would lose its operand, so the partition refuses. -/
def refusesRetainedRead : Option (Bool × Bool) := do
  let ⟨_, _, state⟩ ← seed?
  let source ← interleave? state.cfg
  let uses ← sourceUses 1 0 (source.block .header)
  let reads := uses.any fun
    | .ordinary point => point.cut == 3
    | .phi .. => false
  pure (reads, (sink? source [false, true, false, false, false, true]).isNone)

def refusesGuard : Option (Bool × Bool) := do
  let ⟨_, _, state⟩ ← seed?
  let source ← interleave? state.cfg
  let moveGuard := true :: mask.drop 1
  pure ((partitionFrom? 0 0 moveGuard (source.block .header)).isSome, (sink? source moveGuard).isNone)

/-- The original exit result also appears in the true feedback packet. -/
def refusesFeedback : Option (Bool × Bool) := do
  let .ok (.two record middle moved) := replay feedbackLoop first.header [producer, consumer] | none
  let state ← initial? (Step.fromTwo record middle moved)
  let source ← interleave? state.cfg
  pure ((partitionFrom? 0 0 mask (source.block .header)).isSome, (sink? source mask).isNone)

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Example
