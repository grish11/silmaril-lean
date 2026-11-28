module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.Example.Defs

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.Regression

open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.Example

#guard dependentInitiallyRefused
#guard observe 3 == some {
  requests := [⟨5, 1⟩, ⟨6, 2⟩, ⟨7, 3⟩]
  stop := .fixedPoint
  remainingOrigins := [3, 0, 4]
  slots := [some 1, some 2, some 3, some 0, some 4]
  packets := [[9, 5, 4, 3, 2, 3], [9, 5, 4, 3, 2, 7], [9, 5, 4, 3, 2, 11], [9]]
  runs := [none, none, some 9]
  appendRuns := [none, none, some 9] }
#guard (observe 0).map (fun out => (out.stop, out.requests)) == some (.bound, [])
#guard (observe 2).map (fun out => (out.stop, out.requests)) == some (.bound, [⟨5, 1⟩, ⟨6, 2⟩])
#guard observe 6 == observe 3
#guard refused == some [.prefix, .shape]

-- Both accepted cuts lie in the actual depth-zero entry. The header is depth one.
#guard originFiveCuts == some [1, 2]
#guard modeledDepths == some [0, 1, 0]
#guard observeWith .latest 3 == some {
  requests := [⟨5, 2⟩, ⟨6, 3⟩, ⟨7, 4⟩]
  stop := .fixedPoint
  remainingOrigins := [3, 0, 4]
  slots := [some 0, some 1, some 2, some 3, some 4]
  packets := [[9, 5, 4, 3, 2, 3], [9, 5, 4, 3, 2, 7], [9, 5, 4, 3, 2, 11], [9]]
  runs := [none, none, some 9]
  appendRuns := [none, none, some 9] }

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.Regression
