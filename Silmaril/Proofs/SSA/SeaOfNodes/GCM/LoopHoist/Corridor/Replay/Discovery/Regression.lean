module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Example.Defs
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Regression

open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Example
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Example (first)
open Silmaril.SSA.SeaOfNodes.GCM (Point)

#guard (observe chain).toOption == some ([(1, 0), (2, 1), (5, 2)], [3, 0, 4], none, [none, none, some 5])
#guard (observe immutableSecond).toOption == some ([(1, 0), (2, 1), (5, 2)], [3, 0, 4], none,
  [none, none, some 6])
#guard (observe immutableLater).toOption == some ([(1, 0), (2, 1), (5, 2)], [3, 0, 4], none,
  [none, none, some 3])
#guard (observe varying).toOption == some ([(1, 0)], [3, 0, 2, 4], none, [none, some 13, some 13])
#guard (observe unsaved).toOption == some ([], [0, 1, 2, 3], none, [none, none, some 23])
#guard immutableInterval == some (0, [0, 1], [0, 1])
#guard savedInterval == some (1, [1, 2], [1, 2])
#guard rejectedIntervals
-- Cut 1 is legal for the dependent binding, but discovery still replays at cut 2.
#guard ((discover Step.Example.loopWithOlderSave first.header).toOption.map (·.requests)) ==
  some [⟨1, 0⟩, ⟨2, 1⟩, ⟨5, 2⟩]
#guard (match discover (AfterReorder.Second.Example.loop false) first.header with
  | .ok ⟨requests, .initial (.two _ _ _)⟩ => requests == [⟨1, 0⟩, ⟨2, 1⟩]
  | _ => false)

-- Immediately after the first move, origin 2 reads two immutable inputs.
-- The original dependent-only scan refuses it. The enriched phase emits it.
#guard (match Replay.replay (Step.Example.loopWith true false) first.header [⟨1, 0⟩] with
  | .ok (.one record) =>
    (AfterReorder.Second.findCandidate? 2 0 AfterReorder.Second.savedOrigins (record.output.2.block .header)).isNone &&
      match Replay.second? record ⟨2, 1⟩ with
      | .ok move => move.prepared.consumer.immutableInputs?.isSome &&
          move.prepared.consumer.operands.map Point.cut == [0, 0]
      | .error _ => false
  | _ => false)

-- The continuation likewise reads only cut-zero inputs, but physically
-- inserts at cut two on the current two-save CFG.
#guard (match Replay.replay (Step.Example.loopWith false true) first.header [⟨1, 0⟩, ⟨2, 1⟩] with
  | .ok (.two record request move) =>
    let state := Step.fromTwo record request move
    match Step.emit state ⟨5, 2⟩ with
    | .ok edit => edit.candidate.immutableInputs?.isSome && edit.candidate.operands.map Point.cut == [0, 0]
    | .error _ => false
  | _ => false)

-- Origin 2 survives, but its other operand depends on the latch. Its
-- request uses the correct one-save cut and still fails the actual checker.
#guard (match varying with
  | .ok ⟨_, .initial (.one record)⟩ =>
    record.origins[2]? == some 2 &&
      match Replay.second? record ⟨2, 1⟩ with
      | .error .rejected => true
      | _ => false
  | _ => false)

-- The old two-hoist emitter cannot move the third binding before its
-- second prerequisite is saved. Discovery checks it on the actual seed.
#guard (match Replay.replay Step.Example.loop first.header [⟨1, 0⟩, ⟨5, 1⟩] with
  | .error (.nomination 1 _ .rejected) => true
  | _ => false)

example {plan : Plan _ _ _} (accepted : chain = .ok plan) :
    Step.replayAll Step.Example.loop first.header plan.requests = .ok plan.output :=
  (discover_spec accepted).1

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Regression
