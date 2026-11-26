module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Example.Defs

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Regression

open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Example
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (evalOp lower)

private def source := lower (loop false)

private def sites (dependent : Bool) : Option
    (List (Point (SourceLabel word word)) × List (Use (SourceLabel word word))) := do
  let ⟨_, binding⟩ ← findBinding 1 0 headerOrigins ((lower (loop dependent)).block .header)
  pure (binding.operands, binding.uses)

-- The nominated addition feeds an ordinary read and the false edge's exit Φ operand.
example : sites false = some ([⟨none, 0⟩, ⟨none, 0⟩],
    [.ordinary ⟨headerId, 3⟩, .phi headerId .onFalse 0]) := by cbv
example : sites true = some ([⟨headerId, 1⟩, ⟨none, 0⟩],
    [.ordinary ⟨headerId, 3⟩, .phi headerId .onFalse 0]) := by cbv
example : (Use.phi (Label := SourceLabel word word) headerId .onFalse 0).point? source =
    some ⟨headerId, 4⟩ := by cbv

-- Both blocks offer legal cuts. Depth zero wins over the deeper header address.
private def legalCuts (dependent : Bool) : Option (List Bool) := do
  let tree ← LoopHoist.Corridor.synthesizedTree? (loop dependent)
  let (operands, uses) ← sites dependent
  pure ([⟨none, 0⟩, ⟨headerId, 1⟩].map (checkPlacement tree.1 operands uses))

#guard legalCuts false == some [true, true]
#guard legalCuts true == some [false, true]

-- Move one binding across blocks. The budget-two run takes both feedbacks.
#guard ((shape source none).bindings, (shape source headerId).bindings) == (2, 4)
#guard observe false == (some (0, 0), some (3, 3, [none, none, some 2]))
#guard observe true == (some (1, 1), none)
#guard ((LoopHoist.Corridor.pickAndHoist? (loop false) 1).bind fun (_, output) =>
    (output.2.run evalOp 3 (input 8 8 3)).map (fun env => (env.get .here).toNat)) == some 6

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Regression
