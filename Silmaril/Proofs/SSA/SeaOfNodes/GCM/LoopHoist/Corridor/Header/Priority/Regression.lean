module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.Example.Defs

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.Regression

open Silmaril.MLIR.Arith (Env)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.SSA.SeaOfNodes.GCM (Point)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist (SourceLabel findBinding headerOrigins)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.Example
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Example (word Inputs input opOrder)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (TargetOp evalOp lower)

private def afterFirst := (choose? (Header.Sequence.initial (lower loop)) 3).map Prod.snd

-- After the comparison moves, stale index two names the feedback multiply.
-- That multiply's input from the preceding addition is available at cut two.
#guard (afterFirst.map (fun state => state.origins)) == some [3, 0, 1, 2]
#guard (afterFirst.bind fun state => resolve? state 2) == some 3
#guard ((afterFirst.bind fun state => do
    let ⟨_, binding⟩ ← findBinding 2 0 headerOrigins (state.cfg.block .header)
    pure (binding.operands.map Point.cut))) == some [2, 0]
#guard (afterFirst.bind fun state => choose? state 2).isNone
#guard (afterFirst.bind fun state => (choose? state 3).map (fun (request, _) =>
    (request.binding, request.cut))) == some (3, 0)

-- The same numeric request can select distinct identities on successive CFGs.
-- The final priority (origin one) has no earlier cut and contributes no request.
#guard observe [3, 2, 1] ==
    some ([(3, 0), (3, 0)], ["muli", "ult", "addi", "muli"], [none, none, some 9])
#guard ((schedule? loop [3, 2, 1]).bind fun (requests, _) =>
    (Header.Sequence.schedule? loop requests).map fun cfg => opOrder (cfg.block .header)) ==
    some ["muli", "ult", "addi", "muli"]
#guard observe [1] == some ([], ["addi", "muli", "muli", "ult"], [none, none, some 9])
#guard (observe [3, 3]).isNone
#guard (observe [3, 9]).isNone

private def transfer (cfg : Cfg TargetOp (SourceLabel word word) Inputs [word])
    (old : BitVec 8) : Option (Nat × Nat) :=
  match (cfg.block .header).eval evalOp (fun term env => term.eval env)
      (Env.cons old (input 1 3 1)) with
  | .inl ⟨.header, .cons next .nil⟩ => some (1, next.toNat)
  | .inl ⟨.exit, .cons value .nil⟩ => some (2, value.toNat)
  | .inr _ => none

#guard [transfer (lower loop) 2, transfer (lower loop) 3] == [some (1, 3), some (2, 9)]
#guard ((schedule? loop [3, 2, 1]).map fun (_, cfg) => [transfer cfg 2, transfer cfg 3]) ==
    some [some (1, 3), some (2, 9)]

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.Regression
