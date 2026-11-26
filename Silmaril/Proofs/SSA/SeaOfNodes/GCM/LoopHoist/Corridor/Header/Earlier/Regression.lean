module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.Example.Defs

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.Regression

open Silmaril.MLIR.Arith (Env)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header (swapAt?)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.Example
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Example (word Inputs input opOrder)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (TargetOp evalOp lower)

private def sites (blocked : Bool) :
    Option (List (Point (SourceLabel word word)) × List (Use (SourceLabel word word))) := do
  let ⟨_, binding⟩ ← findBinding 3 0 headerOrigins ((lower (loop blocked)).block .header)
  pure (binding.operands, binding.uses)

example : sites false = some ([⟨headerId, 1⟩, ⟨none, 0⟩], [.phi headerId .onTrue 0]) := by cbv
example : sites true = some ([⟨headerId, 2⟩, ⟨none, 0⟩], [.phi headerId .onTrue 0]) := by cbv
example : (Use.phi (Label := SourceLabel word word) headerId .onTrue 0).point? (lower (loop false)) =
    some ⟨headerId, 5⟩ := by cbv

#guard opOrder ((lower (loop false)).block .header) == ["addi", "muli", "muli", "addi", "ult"]
#guard (swapAt? 2 ((lower (loop false)).block .header)).map opOrder ==
    some ["addi", "muli", "addi", "muli", "ult"]
#guard observe false ==
    some ((1, 1), ["addi", "addi", "muli", "muli", "ult"], [none, none, some 72])

-- The first swap succeeds, but the next one would cross the definition of
-- an operand. A request to emit both swaps fails as a whole.
#guard (swapAt? 2 ((lower (loop true)).block .header)).isSome
#guard (moveAt? (lower (loop true)) 3 ⟨headerId, 1⟩).isNone
#guard observe true ==
    some ((1, 2), ["addi", "muli", "addi", "muli", "ult"], [none, none, some 132])

private def transfer (cfg : Cfg TargetOp (SourceLabel word word) Inputs [word])
    (old : BitVec 8) : Option (Nat × Nat) :=
  match (cfg.block .header).eval evalOp (fun term env => term.eval env)
      (Env.cons old (input 2 6 1)) with
  | .inl ⟨.header, .cons next .nil⟩ => some (1, next.toNat)
  | .inl ⟨.exit, .cons value .nil⟩ => some (2, value.toNat)
  | .inr _ => none

#guard [transfer (lower (loop false)) 4, transfer (lower (loop false)) 6] ==
    [some (1, 6), some (2, 72)]
#guard ((pickAndMove? (loop false) 3).map fun (_, cfg) => [transfer cfg 4, transfer cfg 6]) ==
    some [some (1, 6), some (2, 72)]
#guard ((pickAndMove? (loop false) 3).bind fun (_, cfg) =>
    (cfg.run evalOp 3 (input 6 6 1)).map (fun env => (env.get .here).toNat)) == some 216

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.Regression
