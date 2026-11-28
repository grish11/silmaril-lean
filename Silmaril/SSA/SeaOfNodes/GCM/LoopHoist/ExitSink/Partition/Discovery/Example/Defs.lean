module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Discovery.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Example.Defs

/-! # Discover the interleaved placement from actual feedback and guard reads -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Discovery.Example

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Block Terminator)
open Loop.MLIR.CF (TargetOp evalOp)
open Corridor.Example (Inputs word input)
open Corridor.Header.Typed (edgePackets)
open Corridor.Replay
open Corridor.AfterReorder.Second.Example (first)
open Corridor.Replay.Example (producer consumer)
open Corridor.Replay.Step.Example (words)
open Corridor.Replay.Step.Layout (initial?)
open Corridor.Replay.Step.Layout.Example (seed?)
open ExitSink.Example (feedbackLoop runs)
open Partition.Example (interleave?)

variable {extra : List Width} {saved carried result : Width}

def directReads? : {Γ : List Width} →
    Block TargetOp (Label saved carried result extra) Γ [result] → Option (List Nat)
  | _, .terminator term => roots? term
  | _, .letOp _ _ tail => directReads? tail

structure Observation where
  directOrigins : List Nat
  required : List Nat
  moved : List Nat
  mask : List Bool
  originalPackets : List (List Nat)
  restoredPackets : List (List Nat)
  originalRuns : List (Option Nat)
  emittedRuns : List (Option Nat)
  deriving BEq, Repr

def observe : Option Observation := do
  let ⟨_, _, state⟩ ← seed?
  let source ← interleave? state.cfg
  let .ok plan := discover source | none
  let [test, step, feedback, producerId, consumerId, returned] := state.reference.origins | none
  let origins := [test, producerId, step, consumerId, feedback, returned]
  let direct ← directReads? (source.block .header)
  let inputs := input 2 10 1
  let .inl ⟨.header, packet⟩ := source.entry.eval evalOp (fun term vals => Terminator.eval vals term) inputs | none
  let before := (source.block .header).eval evalOp edgePackets (packet.append inputs)
  let after := (plan.cfg.block .header).eval evalOp edgePackets (packet.append inputs)
  pure ⟨direct.filterMap (fun index => origins.reverse[index]?),
    selected false plan.scan.mask origins, selected true plan.scan.mask origins, plan.scan.mask,
    before.map (fun (_, frame) => words frame.args),
    after.map (fun (_, frame) => words (plan.emission.sunk.restorePacket frame).args),
    runs source, runs plan.cfg⟩

/-- The first feedback argument, rather than the last, needs the add.
The guard needs the comparison. Both bindings must stay in the header. -/
def allRequired : Source Inputs word word word [] where
  entry := .terminator (.br ⟨.header, .cons .here (.cons (.there .here) .nil)⟩)
  block
    | .header =>
      .letOp (.original (.binary word .addi)) (.cons .here (.cons (.there .here) .nil))
        (.letOp (.ult word) (.cons .here (.cons (.there .here) .nil))
          (.terminator (.condBr .here
            ⟨.header, .cons (.there .here) (.cons (.there (.there (.there .here))) .nil)⟩
            ⟨.exit, .cons (.there .here) .nil⟩)))
    | .exit => .terminator (.ret (.cons .here .nil))

def noMove : Option (List Bool × Bool) := do
  let scan ← scan? (allRequired.block .header)
  let refused := match discover allRequired with | .error .noMove => true | _ => false
  pure (scan.mask, refused)

/-- The returned binding also feeds back. The closure still proposes
unneeded lets, but they cannot deliver the exit result required by the emitter. -/
def exitRefusal : Option (List Bool × Bool) := do
  let .ok (.two record middle moved) := replay feedbackLoop first.header [producer, consumer] | none
  let state ← initial? (Step.fromTwo record middle moved)
  let source ← interleave? state.cfg
  let scan ← scan? (source.block .header)
  let refused := match discover source with | .error .partition => true | _ => false
  pure (scan.mask, refused)

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Discovery.Example
