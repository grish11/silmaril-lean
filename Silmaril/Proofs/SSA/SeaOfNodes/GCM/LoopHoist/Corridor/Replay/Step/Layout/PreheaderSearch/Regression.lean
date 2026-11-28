module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Example.Defs

open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Example

#guard observe == some {
  physicalCuts := [1, 2]
  refusedZero := true
  visitedHeader := [1, 2, 3]
  nominatedPoint := (1, 3)
  selectedPoint := (0, 2)
  depths := (0, 1)
  earlierSlot := some 1
  latestSlot := some 0
  beforeEdges := [(1, [3, 2, 7]), (2, [4])]
  afterEdges := [(1, [4, 3, 2, 7]), (2, [4])]
  beforePackets := [[3, 2, 3], [3, 2, 7], [3, 2, 11], [4]]
  afterPackets := [[4, 3, 2, 3], [4, 3, 2, 7], [4, 3, 2, 11], [4]]
  beforeRuns := [none, none, some 4]
  afterRuns := [none, none, some 4]
}

#guard refused == some (true, true, true, 1)
