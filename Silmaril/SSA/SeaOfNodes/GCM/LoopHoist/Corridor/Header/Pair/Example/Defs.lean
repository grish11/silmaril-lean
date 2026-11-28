module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.Example.Defs

/-! # A later placement followed by an earlier placement -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair.Example

open Loop.MLIR.CF (evalOp lower)
open Header.Example (input opOrder)

abbrev loop := Later.Example.loop false

/-- Move the addition after the two multiplies. -/
def first : Request := ⟨0, 3⟩

/-- Move the comparison to the front of the resulting header. -/
def earlierSecond : Request := ⟨3, 0⟩

/-- The same coordinates describe a legal move on the input. In the
current header binding zero is the multiply read at cut one. -/
def blockedSecond : Request := ⟨0, 2⟩

/-- Show the source, intermediate and final opcode order. The final result
contains the observations at CFG fuels three, four and five. -/
def observe (second : Request) :
    List String × Option (List String) × Option (List String × List (Option Nat)) :=
  (opOrder ((lower loop).block .header),
    (move? (lower loop) first).map (fun cfg => opOrder (cfg.block .header)),
    (schedule? loop first second).map fun cfg =>
      (opOrder (cfg.block .header), [3, 4, 5].map fun fuel =>
        (cfg.run evalOp fuel (input 2 4 1)).map (fun env => (env.get .here).toNat)))

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair.Example
