module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Suffix.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.Defs

/-! # Sink a checked stable partition of the saved header -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Block)
open Loop.MLIR.CF (TargetOp)
open Corridor.Header.Earlier (operations)

variable {Labels : List Width → Type} {Γ Result Input extra : List Width}
variable {saved carried result : Width}

/-- Cross the pending moved bindings from right to left. Every swap
rechecks the retained binding's operands in the current typed header. -/
def pullRetained? (kept : Nat) : Nat → Block TargetOp Labels Γ Result → Option (Block TargetOp Labels Γ Result)
  | 0, code => some code
  | pending + 1, code => do
    let crossed ← Corridor.Header.Typed.swapAt? (kept + pending) code
    pullRetained? kept pending crossed

/-- The processed prefix consists of the retained bindings followed by
the pending moved bindings. The mask reads the untouched suffix in its
original order. A true bit sends that binding to the exit. -/
def partitionFrom? : Nat → Nat → List Bool →
    Block TargetOp Labels Γ Result → Option (Block TargetOp Labels Γ Result)
  | _, _, [], code => some code
  | kept, pending, true :: rest, code => partitionFrom? kept (pending + 1) rest code
  | kept, pending, false :: rest, code => do
    let pulled ← pullRetained? kept pending code
    partitionFrom? (kept + 1) pending rest pulled

/-- Select one side of the mask in the original binding order. -/
def selected {α : Type} (side : Bool) (mask : List Bool) (values : List α) : List α :=
  ((mask.zip values).filter fun (move, _) => move == side).map Prod.snd

abbrev HeaderBlock (Input : List Width) (saved carried result : Width) (extra : List Width) :=
  Block TargetOp (Label saved carried result extra) (SavedBank saved carried extra ++ Input) [result]

def withHeader (source : Source Input saved carried result extra)
    (header : HeaderBlock Input saved carried result extra) : Source Input saved carried result extra where
  entry := source.entry
  block
    | .header => header
    | .exit => source.block .exit

structure Emission (source : Source Input saved carried result extra) (mask : List Bool) where
  size : mask.length = (operations (source.block .header)).length
  header : HeaderBlock Input saved carried result extra
  partitioned : partitionFrom? 0 0 mask (source.block .header) = some header
  sunk : Suffix.Emission (withHeader source header) (mask.count false)
  checked : Suffix.sinkAt? (withHeader source header) (mask.count false) = some sunk

variable {source : Source Input saved carried result extra} {mask : List Bool}

abbrev Emission.cfg (emission : Emission source mask) := emission.sunk.cfg

/-- Apply a mask covering exactly the current typed header. The suffix
emitter checks the translated split, exact exit uses, guard and feedback.
Any refusal returns no CFG. -/
def sink? (source : Source Input saved carried result extra) (mask : List Bool) : Option (Emission source mask) := do
  if size : mask.length = (operations (source.block .header)).length then
    match partitioned : partitionFrom? 0 0 mask (source.block .header) with
    | none => none
    | some header =>
      match checked : Suffix.sinkAt? (withHeader source header) (mask.count false) with
      | none => none
      | some sunk => some ⟨size, header, partitioned, sunk, checked⟩
  else none

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition
