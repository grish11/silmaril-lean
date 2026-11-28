module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Example.Defs

/-! # Rank two real blocks for one live binding in a lowered loop -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.Example

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg Frame Terminator)
open Loop.MLIR.CF (TargetOp evalOp)
open Corridor.Example (Inputs word input)
open AfterReorder.Second.Example (first)
open Replay.Example (producer consumer)
open Step.Example (words)

/-- Origin five has ordinary reads in the header and supplies the false-edge
    exit argument directly. -/
def loop := { Layout.Example.loop with result := .output (5 : Fin 8) .head }

def seed? : Option ((saved : Width) × (second : Width) × Layout.State Inputs saved word word [second]) := do
  let .ok (.two record middle two) := replay loop first.header [producer, consumer] | none
  let seed ← Layout.initial? (Step.fromTwo record middle two)
  pure ⟨_, _, seed⟩

def packets {saved : Width} {extra : List Width}
    (cfg : Cfg TargetOp (Label saved word word extra) Inputs [word]) : Option (List (List Nat)) := do
  let inputs := input 2 10 1
  let .inl entry := cfg.entry.eval evalOp (fun term env => Terminator.eval env term) inputs | none
  let step := fun (frame : Frame _) =>
    (cfg.block frame.label).eval evalOp (fun term env => Terminator.eval env term) (frame.args.append inputs)
  let .inl once := step entry | none
  let .inl twice := step once | none
  let .inl exit := step twice | none
  pure ([entry, once, twice, exit].map (fun frame => words frame.args))

def runs {saved : Width} {extra : List Width}
    (cfg : Cfg TargetOp (Label saved word word extra) Inputs [word]) : List (Option Nat) :=
  [3, 4, 5].map fun fuel =>
    (cfg.run evalOp fuel (input 2 10 1)).map (fun env => (env.get .here).toNat)

structure Observation where
  depths : Nat × Nat
  keptCut : Nat × Nat
  rankedCut : Nat × Nat
  headerLater : Bool
  operandCuts : List (Nat × Nat)
  ordinaryReadCuts : List Nat
  falseEdgeRead : Bool
  keptPackets : List (List Nat)
  rankedPackets : List (List Nat)
  keptRuns : List (Option Nat)
  rankedRuns : List (Option Nat)
  deriving BEq, Repr

/-- The later control position loses once loop depth is included. -/
def observe : Option Observation := do
  let ⟨_, _, state⟩ ← seed?
  let ranked ← analyze? state ⟨5, 1⟩
  let keptPackets ← packets state.cfg
  let movedPackets ← packets ranked.output.2.cfg
  let address := ranked.control.tree.address
  let head := ranked.kept.point
  let picked := ranked.point
  let ordinaryReads := ranked.kept.sites.uses.filterMap fun use =>
    match use with | .ordinary point => some point.cut | .phi .. => none
  let falseRead := ranked.kept.sites.uses.any fun use =>
    match use with | .phi (some ⟨_, .header⟩) .onFalse 0 => true | _ => false
  pure ⟨(ranked.control.depth none, ranked.control.depth head.block),
    (blockNumber head.block, head.cut), (blockNumber picked.block, picked.cut),
    decide ((address none).length < (address head.block).length),
    ranked.kept.sites.operands.map (fun point => (blockNumber point.block, point.cut)),
    ordinaryReads, falseRead, keptPackets, movedPackets, runs state.cfg, runs ranked.output.2.cfg⟩

/-- Keep a live binding when its latch operand refuses the preheader splice. -/
def refused : Option (Bool × Bool × Nat) := do
  let ⟨_, _, state⟩ ← seed?
  let ranked ← analyze? state ⟨0, 1⟩
  pure ⟨ranked.kept.sites.operands.any (fun site => blockNumber site.block == 1),
    ranked.preheader.isNone, blockNumber ranked.point.block⟩

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.Example
