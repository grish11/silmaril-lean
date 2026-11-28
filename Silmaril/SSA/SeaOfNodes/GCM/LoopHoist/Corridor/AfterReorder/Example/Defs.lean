module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Example.Defs

/-! # Reorder the comparison, then hoist the captured addition -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Example

open Loop.MLIR.CF (evalOp lower)
open Corridor.Example (loop input)
open Header.Sequence (initial)

def reordered := Header.Priority.plan? (initial (lower (loop false))) [2]

/-- Show the replay coordinates and preheader/header binding counts, and
the emitted CFG's results at fuels three, four and five. -/
def observe (origin : Nat) :
    Option (List (Nat × Nat) × Nat × Nat × List (Option Nat)) :=
  (schedule? (loop false) [2] origin).map fun (plan, output) =>
    (plan.header.map (fun request => (request.binding, request.cut)),
      (shape output.2 none).bindings, (shape output.2 (some ⟨_, .header⟩)).bindings,
      [3, 4, 5].map fun fuel =>
        (output.2.run evalOp fuel (input 2 8 1)).map (fun env => (env.get .here).toNat))

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Example
