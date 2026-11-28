module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Example.Defs
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.Example.Defs
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Regression

open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Example
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Example (first loop)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (lower)

#guard observe [] == .ok ([3, 0, 1, 2, 4], [none, none, some 3])
#guard observe [producer] == .ok ([3, 0, 2, 4], [none, none, some 3])
#guard observe [producer, consumer] == .ok ([3, 0, 4], [none, none, some 3])
#guard locate [producer] 2 == .ok (some (.inl 2))
#guard locate [producer] 1 == .ok (some (.inr (0, 1)))
#guard locate [producer, consumer] 1 == .ok (some (.inr (1, 1)))
#guard locate [producer, consumer] 2 == .ok (some (.inr (0, 2)))
#guard locate [producer, consumer] 4 == .ok (some (.inl 2))
#guard locate [producer, consumer] 5 == .ok none

#guard AfterReorder.Second.Emit.Example.observe false ==
  some (2, (4, 3), [[3, 2, 3], [3, 2, 7], [3, 2, 11], [3]])

example : replay (loop false) [] [] = .ok (.zero (Header.Sequence.initial (lower (loop false)))) := rfl

#guard (match replay (loop false) first.header [producer, consumer] with
  | .ok (.two first second moved) =>
    (first.index, first.cut.block.isNone, first.cut.cut, moved.prepared.index, (secondCut second moved).cut)
  | _ => (99, false, 99, 99, 99)) == (2, true, 0, 2, 1)

-- Exact typed emission equality on this fixture, including the CFG field.
example {record : First _ _ _} {moved : AfterReorder.Second.Emit.Emission _ _ _}
    (accepted : replay (loop false) first.header [producer, consumer] = .ok (.two record consumer moved)) :
    AfterReorder.Second.Emit.replay? (loop false) first 2 = some moved :=
  replay_two_eq accepted

private def refused (varying : Bool) (requests : List Nomination) : Option Refusal :=
  match replay (loop varying) first.header requests with
  | .ok _ => none
  | .error refusal => some refusal

-- Report the first failure even when the suffix would also fail.
#guard refused false [producer, ⟨2, 0⟩, consumer] == some (.nomination 1 ⟨2, 0⟩ (.wrongCut 1))
#guard refused false [⟨2, 0⟩, ⟨1, 1⟩] == some (.nomination 0 ⟨2, 0⟩ .rejected)
#guard refused false [producer, ⟨1, 1⟩] == some (.nomination 1 ⟨1, 1⟩ .rejected)
#guard refused false [producer, ⟨3, 1⟩] == some (.nomination 1 ⟨3, 1⟩ .rejected)
#guard refused true [producer, consumer] == some (.nomination 1 consumer .rejected)
#guard refused false [producer, consumer, ⟨4, 2⟩] == some (.nomination 2 ⟨4, 2⟩ .capacity)

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Regression
