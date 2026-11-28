module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Example.Defs
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Regression

open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Example
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Example (producer consumer)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Example (first)
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Example (word)

example {record : First _ _ _} {moved : AfterReorder.Second.Emit.Emission _ _ _}
    (accepted : replay loop first.header [producer, consumer] = .ok (.two record consumer moved)) :
    Step.replayAll loop first.header [producer, consumer] = .ok (.initial (.two record consumer moved)) := by
  simp [Step.replayAll, accepted, Except.map]

#guard sites == .ok (3, [2, 1])
#guard (match replay loop first.header [producer, consumer] with
  | .ok (.two record request moved) =>
    let state := Step.fromTwo record request moved
    match Step.emit state third with
    | .ok edit =>
      let _ := AfterReorder.Second.targetDecEqWith (saved := moved.prepared.intermediate.1)
        (carried := word) (result := word) (extra := [moved.prepared.consumer.width])
      !Dominance.Placement.checkCut state.cfg AfterReorder.Second.intermediateBlocks
        edit.candidate.operands edit.candidate.uses ⟨none, 1⟩
    | .error _ => false
  | _ => false)
#guard ((observe []).toOption.bind id) == some ([3, 0, 4, 5], 4, [[3, 2, 3], [3, 2, 7], [3, 2, 11], [5]],
  [none, none, some 5])
#guard ((observe [third]).toOption.bind id) == some ([3, 0, 4], 5, [[5, 3, 2, 3], [5, 3, 2, 7], [5, 3, 2, 11], [5]],
  [none, none, some 5])

private def refusal (requests : List Nomination) : Option Refusal :=
  match observe requests with
  | .ok _ => none
  | .error reason => some reason

#guard refusal [⟨5, 1⟩, third] == some (.nomination 2 ⟨5, 1⟩ (.wrongCut 2))
#guard refusal [⟨2, 2⟩] == some (.nomination 2 ⟨2, 2⟩ .rejected)
#guard refusal [third, ⟨5, 3⟩, ⟨2, 3⟩] == some (.nomination 3 ⟨5, 3⟩ .rejected)

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Regression
