module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.Example.Defs

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.Regression

open Silmaril.MLIR.Arith (Env)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist (SourceLabel)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.Example
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair (Request)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair.Example (loop first earlierSecond)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Example (word Inputs input opOrder)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (TargetOp evalOp lower)

private abbrev Cfg8 := Cfg TargetOp (SourceLabel word word) Inputs [word]
private def afterTwo := run? (initial (lower loop)) firstTwo

#guard observe firstTwo ==
    some (["ult", "muli", "muli", "addi"], [3, 1, 2, 0], [0, 3], [none, none, some 32])
#guard observe accepted ==
    some (["ult", "muli", "addi", "muli"], [3, 1, 0, 2], [0, 3, 2], [none, none, some 32])
#guard (Header.Pair.schedule? loop first earlierSecond).map (fun cfg => opOrder (cfg.block .header)) ==
    (schedule? loop firstTwo).map (fun cfg => opOrder (cfg.block .header))

-- The addition moved from index zero to current index three. The ordinary
-- emitter can move it again. The sequence rejects its original identity.
#guard (afterTwo.bind fun state => state.origins[3]?) == some 0
#guard (afterTwo.bind fun state => Header.Pair.move? state.cfg ⟨3, 1⟩).isSome
#guard (schedule? loop repeated).isNone

-- Crossing the current multiply's read also rejects the whole sequence.
private def crossesRead : List Request := firstTwo ++ [⟨1, 3⟩]
#guard (schedule? loop crossesRead).isNone

private def transfer (cfg : Cfg8) (old : BitVec 8) : Option (Nat × Nat) :=
  match (cfg.block .header).eval evalOp (fun term env => term.eval env)
      (Env.cons old (input 2 4 1)) with
  | .inl ⟨.header, .cons next .nil⟩ => some (1, next.toNat)
  | .inl ⟨.exit, .cons value .nil⟩ => some (2, value.toNat)
  | .inr _ => none

#guard [transfer (lower loop) 3, transfer (lower loop) 4] == [some (1, 4), some (2, 32)]
#guard ((schedule? loop accepted).map fun cfg => [transfer cfg 3, transfer cfg 4]) ==
    some [some (1, 4), some (2, 32)]
#guard ((schedule? loop accepted).bind fun cfg =>
    (cfg.run evalOp 3 (input 4 4 1)).map (fun env => (env.get .here).toNat)) == some 64

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.Regression
