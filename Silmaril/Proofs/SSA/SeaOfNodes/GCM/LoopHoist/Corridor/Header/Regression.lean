module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Example.Defs

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Regression

open Silmaril.MLIR.Arith (Env)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Example
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (TargetOp evalOp lower)

private def sites (dependent : Bool) :
    Option (List (Point (SourceLabel word word)) × List (Use (SourceLabel word word))) := do
  let ⟨_, binding⟩ ← findBinding 2 0 headerOrigins ((lower (loop dependent)).block .header)
  pure (binding.operands, binding.uses)

example : sites false = some ([⟨headerId, 1⟩, ⟨none, 0⟩], [.phi headerId .onTrue 0]) := by cbv
example : sites true = some ([⟨headerId, 2⟩, ⟨none, 0⟩], [.phi headerId .onTrue 0]) := by cbv
example : (Use.phi (Label := SourceLabel word word) headerId .onTrue 0).point? (lower (loop false)) =
    some ⟨headerId, 4⟩ := by cbv

-- Moving below the old binding would shift a cut; both original-adjacent
-- cuts at 2 and 3 translate back to the original index and are refused.
#guard [1, 2, 3, 4].map (afterRemoval 2) == [1, 2, 2, 3]
#guard observe false == (some (1, 1), ["addi", "muli", "addi", "ult"],
    some (["addi", "addi", "muli", "ult"], [none, none, some 12]))
#guard observe true == (some (1, 2), ["addi", "muli", "addi", "ult"], none)
#guard (swapAt? 1 ((lower (loop true)).block .header)).isNone

private def transfer (cfg : Cfg TargetOp (SourceLabel word word) Inputs [word])
    (old : BitVec 8) : Option (Nat × Nat) :=
  match (cfg.block .header).eval evalOp (fun term env => term.eval env)
      (Env.cons old (input 2 6 1)) with
  | .inl ⟨.header, .cons next .nil⟩ => some (1, next.toNat)
  | .inl ⟨.exit, .cons value .nil⟩ => some (2, value.toNat)
  | .inr _ => none

-- The true slot carries the moved sum and the false slot carries the
-- multiply it crossed. Verify each successor and its remapped operand.
#guard [transfer (lower (loop false)) 4, transfer (lower (loop false)) 6] ==
    [some (1, 6), some (2, 12)]
#guard ((pickAndMove? (loop false) 2).map fun (_, cfg) => [transfer cfg 4, transfer cfg 6]) ==
    some [some (1, 6), some (2, 12)]
#guard ((pickAndMove? (loop false) 2).bind fun (_, cfg) =>
    (cfg.run evalOp 3 (input 6 6 1)).map (fun env => (env.get .here).toNat)) == some 36

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Regression
