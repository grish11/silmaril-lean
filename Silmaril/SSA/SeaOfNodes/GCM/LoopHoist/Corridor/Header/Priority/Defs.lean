module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.Defs

/-! # Greedy earlier placement of original header bindings -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Loop.MLIR.CF (Program TargetOp lower)
open Pair (Request)
open Sequence (State)

variable {Input : List Width} {carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}

/-- Look up an original identity in the current tracked order. -/
def resolve? (state : State Input carried result) (origin : Nat) : Option Nat :=
  state.origins.idxOf? origin

/-- Search all strictly earlier header cuts in increasing order. Accept a
cut only if the existing checked step emits the new CFG and tracked order. -/
def choose? (state : State Input carried result) (index : Nat) :
    Option (Request × State Input carried result) :=
  (List.range index).findSome? fun cut =>
    let request : Request := ⟨index, cut⟩
    (Sequence.step? state request).map fun next => (request, next)

/-- Resolve each priority on the current state. Skip an identity when
there is no accepted earlier cut. An unknown identity fails the plan. -/
def plan? (state : State Input carried result) :
    List Nat → Option (List Request × State Input carried result)
  | [] => some ([], state)
  | origin :: rest => do
    let index ← resolve? state origin
    match choose? state index with
    | none => plan? state rest
    | some (request, next) =>
      let (requests, final) ← plan? next rest
      pure (request :: requests, final)

/-- Process distinct original identities in the supplied order. Return
the emitted CFG together with the checked requests that replay it. -/
def schedule? (g : Program Input carried result entrySigs headerSigs) (priorities : List Nat) :
    Option (List Request × Cfg TargetOp (SourceLabel carried result) Input [result]) :=
  if priorities.Nodup then
    (plan? (Sequence.initial (lower g)) priorities).map fun (requests, final) => (requests, final.cfg)
  else none

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority
