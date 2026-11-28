module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.Defs

/-! # Two checked placements in the current single-latch header -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Loop.MLIR.CF (Program TargetOp lower)

variable {Input : List Width} {carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}

/-- Both indices are in the current header, before the requested removal. -/
structure Request where
  binding : Nat
  cut : Nat

def Request.point (request : Request) : Point (SourceLabel carried result) :=
  ⟨headerId, request.cut⟩

/-- The moved binding's index in the next header. -/
def Request.insertion (request : Request) : Nat :=
  afterRemoval request.binding request.cut

/-- Resolve and check the request in the current CFG and use the existing
emitter for its direction. A no-op position is refused by the later gate. -/
def move? (cfg : Cfg TargetOp (SourceLabel carried result) Input [result])
    (request : Request) : Option (Cfg TargetOp (SourceLabel carried result) Input [result]) :=
  if request.insertion < request.binding then
    if Later.checkBindingCut cfg request.binding request.point then
      Earlier.moveAt? cfg request.binding request.point
    else none
  else Later.moveCfgAt? cfg request.binding request.point

/-- Apply two distinct placements. The second request names a binding and
cut in the header emitted by the first. Return a CFG only when both pass. -/
def schedule? (g : Program Input carried result entrySigs headerSigs) (first second : Request) :
    Option (Cfg TargetOp (SourceLabel carried result) Input [result]) := do
  let middle ← move? (lower g) first
  if second.binding = first.insertion then none else move? middle second

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair
