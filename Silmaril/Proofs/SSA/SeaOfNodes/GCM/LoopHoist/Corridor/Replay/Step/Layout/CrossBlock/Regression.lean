module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.Example.Defs

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.Regression

open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.Example

#guard observe == some {
  depths := (0, 1)
  keptCut := (1, 3)
  rankedCut := (0, 1)
  headerLater := true
  operandCuts := [(0, 0), (0, 1)]
  ordinaryReadCuts := [4, 5]
  falseEdgeRead := true
  keptPackets := [[3, 2, 3], [3, 2, 7], [3, 2, 11], [4]]
  rankedPackets := [[4, 3, 2, 3], [4, 3, 2, 7], [4, 3, 2, 11], [4]]
  keptRuns := [none, none, some 4]
  rankedRuns := [none, none, some 4] }
#guard refused == some (true, true, 1)

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.Regression
