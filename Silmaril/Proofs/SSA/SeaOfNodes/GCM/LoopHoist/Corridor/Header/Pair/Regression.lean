module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair.Example.Defs

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair.Regression

open Silmaril.MLIR.Arith (Env)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair.Example
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Example (word Inputs input)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (TargetOp evalOp lower)

private abbrev Cfg8 := Cfg TargetOp (SourceLabel word word) Inputs [word]
private def firstResult := move? (lower loop) first

#guard observe earlierSecond ==
    (["addi", "muli", "muli", "ult"], some ["muli", "muli", "addi", "ult"],
      some (["ult", "muli", "muli", "addi"], [none, none, some 32]))

private def readCuts (cfg : Cfg8) (index : Nat) : Option (List (Option Nat)) := do
  let ⟨_, binding⟩ ← findBinding index 0 headerOrigins (cfg.block .header)
  pure (binding.uses.map fun use => (use.point? cfg).map Point.cut)

-- Original index zero is read on the backedge. After the first move,
-- index zero names a multiply with an ordinary read at cut one.
#guard readCuts (lower loop) 0 == some [some 4]
#guard (firstResult.bind fun middle => readCuts middle 0) == some [some 1]
#guard (move? (lower loop) blockedSecond).isSome
#guard (firstResult.bind fun middle => move? middle blockedSecond).isNone
#guard observe blockedSecond ==
    (["addi", "muli", "muli", "ult"], some ["muli", "muli", "addi", "ult"], none)

-- A legal second relocation of the same binding is refused by the pair.
private def repeatFirst : Request := ⟨2, 1⟩
#guard first.insertion == 2
#guard (firstResult.bind fun middle => move? middle repeatFirst).isSome
#guard (schedule? loop first repeatFirst).isNone

private def transfer (cfg : Cfg8) (old : BitVec 8) : Option (Nat × Nat) :=
  match (cfg.block .header).eval evalOp (fun term env => term.eval env)
      (Env.cons old (input 2 4 1)) with
  | .inl ⟨.header, .cons next .nil⟩ => some (1, next.toNat)
  | .inl ⟨.exit, .cons value .nil⟩ => some (2, value.toNat)
  | .inr _ => none

#guard [transfer (lower loop) 3, transfer (lower loop) 4] == [some (1, 4), some (2, 32)]
#guard ((schedule? loop first earlierSecond).map fun cfg => [transfer cfg 3, transfer cfg 4]) ==
    some [some (1, 4), some (2, 32)]
#guard ((schedule? loop first earlierSecond).bind fun cfg =>
    (cfg.run evalOp 3 (input 4 4 1)).map (fun env => (env.get .here).toNat)) == some 64

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair.Regression
