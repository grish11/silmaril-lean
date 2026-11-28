module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.Example.Defs

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.Regression

open Silmaril.MLIR.Arith (Env)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header (afterRemoval swapAt?)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Example (word Inputs input opOrder)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.Example
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (TargetOp evalOp lower)

private def sites (blocked : Bool) :
    Option (List (Point (SourceLabel word word)) × List (Use (SourceLabel word word))) := do
  let ⟨_, binding⟩ ← findBinding 0 0 headerOrigins ((lower (loop blocked)).block .header)
  pure (binding.operands, binding.uses)

example : sites false = some ([⟨headerId, 0⟩, ⟨none, 0⟩], [.phi headerId .onTrue 0]) := by cbv
example : sites true = some ([⟨headerId, 0⟩, ⟨none, 0⟩],
    [.ordinary ⟨headerId, 2⟩, .phi headerId .onTrue 0]) := by cbv
example : (Use.phi (Label := SourceLabel word word) headerId .onTrue 0).point? (lower (loop false)) =
    some ⟨headerId, 4⟩ := by cbv

-- The old ranking still picks the first feasible cut. The explicit
-- destination at original cut 3 goes to binding index 2 after removal.
#guard rankedCut false == some (1, 0)
#guard afterRemoval 0 3 == 2
#guard opOrder ((lower (loop false)).block .header) == ["addi", "muli", "muli", "ult"]
#guard (swapAt? 0 ((lower (loop false)).block .header)).map opOrder ==
    some ["muli", "addi", "muli", "ult"]
#guard checkDestination (loop false) 0 ⟨headerId, 3⟩
#guard observe false 3 == some (["muli", "muli", "addi", "ult"], [none, none, some 32])

-- Cut 2 is before the multiply's read, while cut 3 follows it.
#guard checkDestination (loop true) 0 ⟨headerId, 2⟩
#guard !(checkDestination (loop true) 0 ⟨headerId, 3⟩)
#guard observe true 2 == some (["muli", "addi", "muli", "ult"], [none, none, some 20])
#guard (observe true 3).isNone
#guard (moveLater? 0 1 ((lower (loop true)).block .header)).isNone

-- Invalid, non-header and no-op coordinates are refused.
#guard !(checkDestination (loop false) 0 ⟨headerId, 5⟩)
#guard !(checkDestination (loop false) 0 ⟨none, 0⟩)
#guard !(checkDestination (loop false) 0 ⟨headerId, 1⟩)

private def transfer (cfg : Cfg TargetOp (SourceLabel word word) Inputs [word])
    (old : BitVec 8) : Option (Nat × Nat) :=
  match (cfg.block .header).eval evalOp (fun term env => term.eval env)
      (Env.cons old (input 2 4 1)) with
  | .inl ⟨.header, .cons next .nil⟩ => some (1, next.toNat)
  | .inl ⟨.exit, .cons value .nil⟩ => some (2, value.toNat)
  | .inr _ => none

#guard [transfer (lower (loop false)) 3, transfer (lower (loop false)) 4] ==
    [some (1, 4), some (2, 32)]
#guard ((moveAt? (loop false) 0 ⟨headerId, 3⟩).map fun cfg => [transfer cfg 3, transfer cfg 4]) ==
    some [some (1, 4), some (2, 32)]
#guard ((moveAt? (loop false) 0 ⟨headerId, 3⟩).bind fun cfg =>
    (cfg.run evalOp 3 (input 4 4 1)).map (fun env => (env.get .here).toNat)) == some 64

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.Regression
