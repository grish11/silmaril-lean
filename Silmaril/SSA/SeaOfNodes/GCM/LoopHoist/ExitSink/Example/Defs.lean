module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Example.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Defs

/-! # Sink the exit-only add of a real lowered, saved loop -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Example

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg Terminator)
open Loop.MLIR.CF (TargetOp evalOp)
open Corridor.Example (Inputs word input)
open Corridor.Header.Typed (edgePackets)
open Corridor.Replay
open Corridor.AfterReorder.Second.Example (first)
open Corridor.Replay.Example (producer consumer)
open Corridor.Replay.Step.Example (words)
open Corridor.Replay.Step.Layout (initial?)
open Corridor.Replay.Step.Layout.Example (loop seed?)

structure Observation where
  headerBindings : Nat × Nat
  exitBindings : Nat × Nat
  beforeEdges : List (List Nat)
  afterEdges : List (List Nat)
  exactPackets : Bool
  beforeRuns : List (Option Nat)
  afterRuns : List (Option Nat)
  deriving BEq, Repr

def runs {Labels : List Width → Type} (cfg : Cfg TargetOp Labels Inputs [word]) : List (Option Nat) :=
  [0, 3, 4, 5].map fun fuel =>
    (cfg.run evalOp fuel (input 2 10 1)).map (fun env => (env.get .here).toNat)

def observe : Option Observation := do
  let ⟨_, _, state⟩ ← seed?
  let index ← state.reference.origins.idxOf? 7
  let sunk ← sink? state.cfg index
  let inputs := input 2 10 1
  let .inl ⟨.header, packet⟩ := state.cfg.entry.eval evalOp (fun term vals => Terminator.eval vals term) inputs | none
  let before := (state.cfg.block .header).eval evalOp edgePackets (packet.append inputs)
  let after := (sunk.cfg.block .header).eval evalOp edgePackets (packet.append inputs)
  let exactPackets := match before, after with
    | [(.onTrue, ⟨.header, oldFeedback⟩), (.onFalse, ⟨.exit, oldExit⟩)],
      [(.onTrue, ⟨.header, newFeedback⟩), (.onFalse, ⟨.exit, operands⟩)] =>
      words oldFeedback == words newFeedback &&
        words oldExit == [(evalOp sunk.header.opcode.2 operands).toNat]
    | _, _ => false
  pure ⟨((shape state.cfg (some ⟨_, .header⟩)).bindings, (shape sunk.cfg (some ⟨_, .header⟩)).bindings),
    ((shape state.cfg (some ⟨_, .exit⟩)).bindings, (shape sunk.cfg exitId).bindings),
    before.map (fun (_, frame) => words frame.args), after.map (fun (_, frame) => words frame.args),
    exactPackets, runs state.cfg, runs sunk.cfg⟩

/-- The same add is now also the next latch value. It must run before the
true-edge transfer, even though the false edge still returns its result. -/
def feedbackLoop := { loop with phiInputs := fun
  | .entry => loop.phiInputs .entry
  | .backedge => .cons (.output (7 : Fin 8) .head) .nil }

def refusesFeedback : Option (Bool × Bool) := do
  let .ok (.two record middle moved) := replay feedbackLoop first.header [producer, consumer] | none
  let state ← initial? (Step.fromTwo record middle moved)
  let index ← state.reference.origins.idxOf? 7
  let readsFeedback := match sourceUses index 0 (state.cfg.block .header) with
    | some [.phi (some ⟨_, .header⟩) .onTrue 2, .phi (some ⟨_, .header⟩) .onFalse 0] => true
    | _ => false
  pure (readsFeedback, (sink? state.cfg index).isNone)

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Example
