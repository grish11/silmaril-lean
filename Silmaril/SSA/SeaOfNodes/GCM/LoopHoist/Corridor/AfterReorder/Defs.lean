module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.Defs

/-! # Reorder a typed header, then hoist one original binding -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder

open Silmaril.MLIR.Arith (Width)
open Loop.MLIR.CF (Program lower)
open Header.Pair (Request)
open Header.Sequence (State)

variable {Input : List Width} {carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}

/-- Replay the current-coordinate header requests, then resolve the
original identity nominated for the preheader hoist. -/
structure Plan where
  header : List Request
  hoistOrigin : Nat

/-- Resolve the original identity on the current typed header. The
existing corridor must select preheader cut zero and the binding must
have captured operands. The input state comes from a header-only plan
on the native loop's lowering, which has the canonical exit. -/
def resolveMove? (state : State Input carried result) (origin : Nat) :
    Option (Nat × Point (SourceLabel carried result) × Output Input carried result) := do
  let index ← Header.Priority.resolve? state origin
  let (cut, output) ← hoistCodeWith? state.cfg.entry (state.cfg.block .header) index (chooseCfgCut? state.cfg)
  pure (index, cut, output)

def finish? (state : State Input carried result) (origin : Nat) : Option (Output Input carried result) :=
  (resolveMove? state origin).map fun (_, _, output) => output

def replay? (g : Program Input carried result entrySigs headerSigs) (plan : Plan) :
    Option (Output Input carried result) := do
  let state ← Header.Sequence.run? (Header.Sequence.initial (lower g)) plan.header
  finish? state plan.hoistOrigin

/-- Run the existing header planner, then attempt one cross-block hoist.
Return the plan and emitted CFG only if both parts succeed. -/
def schedule? (g : Program Input carried result entrySigs headerSigs)
    (priorities : List Nat) (origin : Nat) : Option (Plan × Output Input carried result) :=
  if priorities.Nodup then do
    let (requests, state) ← Header.Priority.plan? (Header.Sequence.initial (lower g)) priorities
    let output ← finish? state origin
    pure (⟨requests, origin⟩, output)
  else none

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder
