module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Run.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Example.Defs

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Run.Example

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.Pure (i1)
open Loop.MLIR.CF (evalOp)
open Corridor.Example (Inputs input word)
open Corridor.Replay.Step.Example (words)
open Corridor.Replay.Step.Layout.Example (seed?)
open Partition.Example (interleave?)
open Partition.Discovery (discover operandIndices)
open Phi.Example (parallelCfg unpackWords?)

variable {Input full extra : List Width} {saved carried result : Width}

structure Observation where
  feedbacks : Nat
  taken : String
  remaining : Nat
  projection : List Nat
  compactReads : List Nat
  fullPacket : List Nat
  compactPacket : List Nat
  latch : List Nat
  output : Nat
  deriving BEq, Repr

/-- Read the row chosen by the actual entry and header evaluations, and
display it only if the ordinary compact CF run returns. -/
def observe? (source : TargetCfg Input saved carried result extra full) (inputs : Env Input)
    (fuel : Nat) : Option Observation := do
  let emission ← compact? source
  if !(admitted emission.cfg inputs) then none else do
    let output ← emission.cfg.run evalOp fuel inputs
    let old ← firstExit? source inputs fuel
    let arrived ← firstExit? emission.cfg inputs fuel
    let row ← operandsAt? emission.cfg (.header, arrived.slot)
    let latched ← (latchAt? emission.cfg (.header, arrived.slot) arrived.env).bind unpackWords?
    let slot := match arrived.slot with
      | .jump => "jump"
      | .onTrue => "true"
      | .onFalse => "false"
    pure ⟨arrived.feedbacks, slot, arrived.remaining, emission.projection.indices,
      operandIndices row, words old.packet, words arrived.packet, latched, (output.get .here).toNat⟩

def withInterleaved {α : Type}
    (observe : ∀ {saved : Width} {extra full : List Width}, TargetCfg Inputs saved word word extra full → Option α) :
    Option α := do
  let ⟨_, _, state⟩ ← seed?
  let source ← interleave? state.cfg
  let .ok plan := discover source | none
  observe plan.cfg

def interleaved (inputs : Env Inputs) (fuel : Nat) : Option Observation :=
  withInterleaved (fun source => observe? source inputs fuel)

def immediate := interleaved (input 4 1 1) 3

def afterFeedback := interleaved (input 2 10 1) 5

def exhausted := interleaved (input 2 10 1) 4

/-- Four blocks suffice to reach the exit after two feedbacks. It takes a
fifth block to execute the exit and produce a return. -/
def arrivedWithoutReturn : Option (Nat × Nat × Bool) :=
  withInterleaved fun source => do
    let emission ← compact? source
    let inputs := input 2 10 1
    let arrived ← firstExit? emission.cfg inputs 4
    pure (arrived.feedbacks, arrived.remaining, (emission.cfg.run evalOp 4 inputs).isNone)

def parallel (taken : BitVec i1.val) : Option Observation :=
  observe? parallelCfg (.cons taken (.cons 7 (.cons 9 .nil))) 3

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Run.Example
