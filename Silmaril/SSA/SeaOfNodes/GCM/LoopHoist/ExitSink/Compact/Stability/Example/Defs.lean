module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Discovery.Example.Defs

/-! # Re-run the existing compactor on the emitted CFG itself -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability.Example

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Block Terminator)
open Loop.MLIR.CF (TargetOp evalOp)
open Corridor.Example (input word)
open Corridor.Header.Typed (edgePackets)
open Corridor.Replay.Step.Example (words)
open Corridor.Replay.Step.Layout.Example (seed?)
open Partition.Example (interleave?)
open Partition.Discovery (discover operandIndices)

variable {Γ extra full Input : List Width} {saved carried result : Width}

/-- Display the positional operands of the actual exit, including the return. -/
def reads : {Γ : List Width} → Block TargetOp (ExitLabel (SavedBank saved carried extra) full) Γ [result] →
    List (List Nat)
  | _, .letOp _ operands tail => operandIndices operands :: reads tail
  | _, .terminator (.ret operands) => [operandIndices operands]
  | _, .terminator _ => []

def packets (cfg : TargetCfg Input saved carried result extra full) (inputs : Env Input) : Option (List (List Nat)) := do
  let .inl ⟨.header, packet⟩ := cfg.entry.eval evalOp (fun term vals => Terminator.eval vals term) inputs | none
  pure (((cfg.block .header).eval evalOp edgePackets (packet.append inputs)).map (fun (_, frame) => words frame.args))

structure Observation where
  firstProjection : List Nat
  secondInputs : List Nat
  secondMask : List Bool
  secondProjection : List Nat
  firstReads : List (List Nat)
  secondReads : List (List Nat)
  firstPackets : List (List Nat)
  secondPackets : List (List Nat)
  deriving BEq, Repr

def observe : Option Observation := do
  let ⟨_, _, state⟩ ← seed?
  let source ← interleave? state.cfg
  let .ok plan := discover source | none
  let first ← compact? plan.cfg
  let second ← compact? first.cfg
  let inputs := input 4 11 1
  let oldPackets ← packets first.cfg inputs
  let newPackets ← packets second.cfg inputs
  pure ⟨first.projection.indices, second.scan.inputs, second.scan.mask, second.projection.indices,
    reads (first.cfg.block .exit), reads (second.cfg.block .exit), oldPackets, newPackets⟩

/-- The source forwards one word, while the exit reads only its ambient input. -/
def ambientLoop : TargetCfg [word] word word word [] [word] where
  entry := .terminator (.br ⟨.header, .cons .here (.cons .here .nil)⟩)
  block
    | .header =>
      .letOp (.ult word) (.cons .here (.cons .here .nil))
        (.terminator (.condBr .here
          ⟨.header, .cons (.there .here) (.cons (.there (.there .here)) .nil)⟩
          ⟨.exit, .cons (.there .here) .nil⟩))
    | .exit => .terminator (.ret (.cons (.there .here) .nil))

def ambientOnly : Option (List Nat × List Nat × List Nat × List (List Nat)) := do
  let first ← compact? ambientLoop
  let second ← compact? first.cfg
  let routed ← packets second.cfg (.cons 7 .nil)
  pure (first.projection.indices, second.scan.inputs, second.projection.indices, routed)

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability.Example
