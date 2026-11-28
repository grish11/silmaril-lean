module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability.Example.Defs

/-! # The compacted exit's actual CF packets and explicit Φ rows -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Example

open Silmaril.MLIR.Arith (Atom Env Width)
open Silmaril.MLIR.CF (Terminator)
open Silmaril.MLIR.Pure (i1)
open Silmaril.Isotope (Value)
open Loop.MLIR.CF (evalOp)
open Corridor.Example (input word)
open Corridor.Replay.Step.Example (words)
open Corridor.Replay.Step.Layout.Example (seed?)
open Partition.Example (interleave?)
open Partition.Discovery (discover operandIndices)

variable {Input full extra : List Width} {saved carried result : Width}

def unpackWords? : Value Atom → Option (List Nat)
  | .unit => some []
  | .pair (.atom ⟨_, bits⟩) rest => (unpackWords? rest).map (bits.toNat :: ·)
  | _ => none

structure RowObservation where
  reads : List Nat
  packet : List Nat
  latched : List Nat
  deriving BEq, Repr

def observeAt? (cfg : TargetCfg Input saved carried result extra full) (occ : Occurrence)
    (env : Env (occ.1.scope Input (SavedBank saved carried extra))) : Option RowObservation := do
  let args ← operandsAt? cfg occ
  let packet ← packetAt? cfg occ env
  let latched ← (latchAt? cfg occ env).bind unpackWords?
  pure ⟨operandIndices args, words packet, latched⟩

structure CompactionObservation where
  projection : List Nat
  full : RowObservation
  compact : RowObservation
  recompacted : RowObservation
  deriving BEq, Repr

def compareAt? (source : TargetCfg Input saved carried result extra full) (occ : Occurrence)
    (env : Env (occ.1.scope Input (SavedBank saved carried extra))) : Option CompactionObservation := do
  let first ← compact? source
  let second ← compact? first.cfg
  pure ⟨first.projection.indices, ← observeAt? source occ env, ← observeAt? first.cfg occ env,
    ← observeAt? second.cfg occ env⟩

def interleaved : Option CompactionObservation := do
  let ⟨_, _, state⟩ ← seed?
  let source ← interleave? state.cfg
  let .ok plan := discover source | none
  let inputs := input 4 11 1
  let .inl ⟨.header, packet⟩ := plan.cfg.entry.eval evalOp (fun t vals => Terminator.eval vals t) inputs | none
  compareAt? plan.cfg (.header, .onFalse) (packet.append inputs)

def ambientOnly : Option (CompactionObservation × Bool) := do
  let source := Stability.Example.ambientLoop
  let env := Env.cons 7 (.cons 7 (.cons 7 .nil))
  let observed ← compareAt? source (.header, .onFalse) env
  let first ← compact? source
  pure (observed, (observeAt? first.cfg (.header, .onTrue) env).isNone)

/-- Both branches in the saved-bank CFG label family target the same exit.
The source operands are swapped, and the exit needs only the first one. -/
def parallelCfg : TargetCfg [i1, word, word] word word word [] [word, word] where
  entry := .terminator (.br ⟨.header, .cons (.there .here) (.cons (.there (.there .here)) .nil)⟩)
  block
    | .header => .terminator (.condBr (.there (.there .here))
        ⟨.exit, .cons .here (.cons (.there .here) .nil)⟩
        ⟨.exit, .cons (.there .here) (.cons .here .nil)⟩)
    | .exit => .terminator (.ret (.cons .here .nil))

def parallel : Option (CompactionObservation × CompactionObservation × List (Option Nat)) := do
  let taken := Env.cons 1 (.cons 7 (.cons 9 .nil))
  let notTaken := Env.cons 0 (.cons 7 (.cons 9 .nil))
  let .inl ⟨.header, packet⟩ :=
    parallelCfg.entry.eval evalOp (fun t vals => Terminator.eval vals t) taken | none
  let first ← compact? parallelCfg
  let outcomes := [taken, notTaken].map fun inputs =>
    (first.cfg.run evalOp 3 inputs).map (fun env => (env.get .here).toNat)
  pure (← compareAt? parallelCfg (.header, .onTrue) (packet.append taken),
    ← compareAt? parallelCfg (.header, .onFalse) (packet.append taken), outcomes)

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Example
