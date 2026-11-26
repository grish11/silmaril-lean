module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.SingleLatch.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery.Example.Defs

open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second (savedHeader)

private def observedDepths : Option ((Nat × Nat × Nat) × (Nat × Nat) × (Nat × Nat × Nat)) := do
  let ⟨_, _, source⟩ ← Example.seed?
  let before ← CrossBlock.Control.check? source
  let ranked ← PreheaderSearch.rank? source 5 2
  let after ← CrossBlock.Control.check? ranked.selection.2.2
  let point := ranked.selection.1
  pure ((before.depth none, before.depth savedHeader, before.depth (some ⟨_, .exit⟩)),
    (CrossBlock.blockNumber point.block, point.cut),
    (after.depth none, after.depth savedHeader, after.depth (some ⟨_, .exit⟩)))

-- The preheader wins even with a nonzero header-walk budget. Control synthesis
-- recognizes the same loop after adding the new word to the header signature.
#guard observedDepths == some ((0, 1, 0), (0, 2), (0, 1, 0))

private def unusedOrigin : Option (List Nat × Bool × Bool × Bool × Bool) := do
  let ⟨_, _, source⟩ ← CrossBlock.Example.seed?
  let plan ← PreheaderSearch.Sequence.Discovery.schedule? ⟨_, source⟩
  let final := plan.output.2
  pure (plan.requests.map PreheaderSearch.Sequence.Request.origin,
    final.reference.origins.contains 7, (PreheaderSearch.latest? final 7).isSome,
    (CrossBlock.keep? final 7).isNone, (PreheaderSearch.Sequence.Discovery.choose? plan.output).isNone)

-- The raw splice checker can move unused origin 7. The scheduler stops
-- after saving the live producer and its consumer in the current header.
#guard unusedOrigin == some ([5, 6], true, true, true, true)
