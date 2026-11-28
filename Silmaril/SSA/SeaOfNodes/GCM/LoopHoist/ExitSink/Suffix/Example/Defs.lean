module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Suffix.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Example.Defs

/-! # Discover three dependent exit-only operations in a lowered saved loop -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Suffix.Example

open Silmaril.MLIR.CF (Terminator)
open Loop.MLIR.CF (evalOp)
open Corridor.Example (input)
open Corridor.Header.Typed (edgePackets)
open Corridor.Replay
open Corridor.AfterReorder.Second.Example (first)
open Corridor.Replay.Example (producer consumer)
open Corridor.Replay.Step.Example (words)
open Corridor.Replay.Step.Layout (initial?)
open Corridor.Replay.Step.Layout.Example (loop seed?)
open ExitSink.Example (feedbackLoop runs)

structure Observation where
  split : Nat
  exitBindings : Nat
  shorterAccepted : Bool
  earlierRefused : Bool
  exitOperandCuts : List (List Nat)
  beforePackets : List (List Nat)
  afterPackets : List (List Nat)
  restoredPackets : List (List Nat)
  beforeRuns : List (Option Nat)
  afterRuns : List (Option Nat)
  deriving BEq, Repr

def observe : Option Observation := do
  let ⟨_, _, state⟩ ← seed?
  let ⟨cut, sunk⟩ ← discover? state.cfg
  let inputs := input 2 10 1
  let .inl ⟨.header, packet⟩ := state.cfg.entry.eval evalOp (fun term vals => Terminator.eval vals term) inputs | none
  let before := (state.cfg.block .header).eval evalOp edgePackets (packet.append inputs)
  let after := (sunk.cfg.block .header).eval evalOp edgePackets (packet.append inputs)
  pure ⟨cut, (shape sunk.cfg exitId).bindings, (sinkAt? state.cfg (cut + 1)).isSome,
    (sinkAt? state.cfg (cut - 1)).isNone,
    (sites exitId 0 (sunk.cfg.block .exit)).map fun site => site.operands.map Point.cut,
    before.map (fun (_, frame) => words frame.args), after.map (fun (_, frame) => words frame.args),
    after.map (fun (_, frame) => words (sunk.restorePacket frame).args), runs state.cfg, runs sunk.cfg⟩

/-- With origin 6 live on feedback, the longer suffix is refused. The
final consumer still moves and reads origin 6 from its operand packet. -/
def retainsFeedbackProducer : Option (Nat × Nat × Bool) := do
  let modified := { loop with phiInputs := fun
    | .entry => loop.phiInputs .entry
    | .backedge => .cons (.output (6 : Fin 8) .head) .nil }
  let .ok (.two record middle moved) := replay modified first.header [producer, consumer] | none
  let state ← initial? (Step.fromTwo record middle moved)
  let index ← state.reference.origins.idxOf? 6
  let ⟨cut, sunk⟩ ← discover? state.cfg
  pure (cut, (shape sunk.cfg exitId).bindings, (sinkAt? state.cfg index).isNone)

/-- If the returning value itself feeds back, there is no supported suffix. -/
def refusesFeedbackResult : Option Bool := do
  let .ok (.two record middle moved) := replay feedbackLoop first.header [producer, consumer] | none
  let state ← initial? (Step.fromTwo record middle moved)
  pure (discover? state.cfg).isNone

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Suffix.Example
