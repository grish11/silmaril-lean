module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair.Example.Defs

/-! # Three distinct placements with a repeated-identity refusal -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.Example

open Loop.MLIR.CF (evalOp lower)
open Header.Example (input opOrder)
open Pair (Request)
open Pair.Example (loop first earlierSecond)

def firstTwo : List Request := [first, earlierSecond]

/-- Move the second multiply later across the previously moved addition. -/
def accepted : List Request := firstTwo ++ [⟨2, 4⟩]

/-- Request the original addition again, this time at current index three. -/
def repeated : List Request := firstTwo ++ [⟨3, 1⟩]

/-- Observe typed operation order, current-to-original indices, the moved
origins in request order, and returns at CFG fuels three, four and five. -/
def observe (requests : List Request) :
    Option (List String × List Nat × List Nat × List (Option Nat)) :=
  (run? (initial (lower loop)) requests).map fun result =>
    (opOrder (result.cfg.block .header), result.origins, result.moved.reverse,
      [3, 4, 5].map fun fuel =>
        (result.cfg.run evalOp fuel (input 2 4 1)).map (fun env => (env.get .here).toNat))

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.Example
