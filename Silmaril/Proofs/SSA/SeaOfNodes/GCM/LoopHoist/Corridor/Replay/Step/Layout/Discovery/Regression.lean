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

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.Regression
