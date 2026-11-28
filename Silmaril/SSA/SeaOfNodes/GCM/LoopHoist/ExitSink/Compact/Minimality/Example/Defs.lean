module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Minimality.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Discovery.Example.Defs

/-! # Compare three checked projections on the actual interleaved exit -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Minimality.Example

open Silmaril.MLIR.CF (Block)
open Loop.MLIR.CF (TargetOp)
open Corridor.Example (Inputs word)
open Corridor.Replay.Step.Layout.Example (seed?)
open Partition.Example (interleave?)
open Partition.Discovery (discover operandIndices)

/-- Slot 4 is needed by a moved producer, and there is no direct return
read of that old slot. Keeping an extra slot is allowed by the rewrite. -/
def observe : Option (List (List Nat × Bool) × List Nat) := do
  let ⟨_, _, state⟩ ← seed?
  let source ← interleave? state.cfg
  let .ok plan := discover source | none
  let emission ← compact? plan.cfg
  let full := plan.emission.sunk.header.packetTypes
  let exitCode := plan.cfg.block .exit
  let .letOp _ firstReads _ := exitCode | none
  let minimal := emission.projection
  let larger := Projection.forReads full (0 :: minimal.indices)
  let smaller := Projection.forReads full (minimal.indices.filter (· != 4))
  pure ([minimal, larger, smaller].map (fun p =>
    (p.indices, (p.rewriteScanned? (Input := Inputs) exitCode).isSome)), operandIndices firstReads)

/-- A direct read of the ambient input needs no forwarded packet slot. -/
def ambientOnly : Bool :=
  let exitCode : Block TargetOp (ExitLabel [] [word]) ([word] ++ [word]) [word] :=
    .terminator (.ret (.cons (.there .here) .nil))
  let empty := Projection.forReads [word] []
  (empty.rewriteScanned? (Input := [word]) exitCode).isSome

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Minimality.Example
