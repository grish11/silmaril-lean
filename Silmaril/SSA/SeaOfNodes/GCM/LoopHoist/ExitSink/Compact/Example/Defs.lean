module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Discovery.Example.Defs

/-! # Compact the exit of the automatically discovered interleaved move -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Example

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Cfg Terminator)
open Loop.MLIR.CF (TargetOp evalOp)
open Corridor.Example (Inputs word input)
open Corridor.Header.Typed (edgePackets renameSuffix)
open Corridor.Replay.Step.Example (words)
open Corridor.Replay.Step.Layout.Example (seed?)
open Partition.Example (interleave?)
open Partition.Discovery (discover operandIndices)

structure Observation where
  selectedSlots : List Nat
  firstProducerReads : List Nat
  fullPackets : List (List Nat)
  compactPackets : List (List Nat)
  projectedPackets : List (List Nat)
  fullExitBindings : Nat
  compactExitBindings : Nat
  fullRuns : List (Option Nat)
  compactRuns : List (Option Nat)
  deriving BEq, Repr

def runsOn {Labels : List Width → Type} (inputs : Env Inputs)
    (cfg : Cfg TargetOp Labels Inputs [word]) : List (Option Nat) :=
  [0, 3, 4, 5].map fun fuel =>
    (cfg.run evalOp fuel inputs).map (fun env => (env.get .here).toNat)

def observeOn (inputs : Env Inputs) : Option Observation := do
  let ⟨_, _, state⟩ ← seed?
  let source ← interleave? state.cfg
  let .ok plan := discover source | none
  let compact ← compact? plan.cfg
  let .letOp _ firstReads _ := plan.cfg.block .exit | none
  let .inl ⟨.header, packet⟩ := plan.cfg.entry.eval evalOp (fun term vals => Terminator.eval vals term) inputs | none
  let before := (plan.cfg.block .header).eval evalOp edgePackets (packet.append inputs)
  let after := (compact.cfg.block .header).eval evalOp edgePackets (packet.append inputs)
  pure ⟨compact.projection.indices, operandIndices firstReads, before.map (fun (_, frame) => words frame.args),
    after.map (fun (_, frame) => words frame.args),
    before.map (fun (_, frame) => words (compact.projection.frame frame).args),
    (shape plan.cfg exitId).bindings, (shape compact.cfg exitId).bindings,
    runsOn inputs plan.cfg, runsOn inputs compact.cfg⟩

def observe : Option Observation := observeOn (input 2 10 1)

/-- Dropping every packet argument would strand a surviving operand of
the discovered exit chain. The actual typed exit rewrite must refuse. -/
def refusesMissingOperand : Option Bool := do
  let ⟨_, _, state⟩ ← seed?
  let source ← interleave? state.cfg
  let .ok plan := discover source | none
  let scan ← scanExit? (plan.cfg.block .exit)
  let proposed := Projection.forReads plan.emission.sunk.header.packetTypes []
  pure (rewriteExit? (kept := proposed.types) scan.mask
    (proposed.rename (Input := Inputs)) (plan.cfg.block .exit)).isNone

/-- Add one dead pure computation reading the first full-packet slot.
It must neither survive compaction nor keep that slot live. -/
def withDeadExit {saved carried result : Width} {extra : List Width} :
    (packet : List Width) → TargetCfg Inputs saved carried result extra packet →
      TargetCfg Inputs saved carried result extra packet
  | [], cfg => cfg
  | width :: _, cfg => { cfg with block := fun
    | .header => cfg.block .header
    | .exit => .letOp (.original (.binary width .addi)) (.cons .here (.cons .here .nil))
        (renameSuffix Var.there (cfg.block .exit)) }

def prunesDeadRead : Option (List Nat × Nat × Nat) := do
  let ⟨_, _, state⟩ ← seed?
  let source ← interleave? state.cfg
  let .ok plan := discover source | none
  let full := withDeadExit _ plan.cfg
  let compact ← compact? full
  pure (compact.projection.indices, (shape full exitId).bindings, (shape compact.cfg exitId).bindings)

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Example
