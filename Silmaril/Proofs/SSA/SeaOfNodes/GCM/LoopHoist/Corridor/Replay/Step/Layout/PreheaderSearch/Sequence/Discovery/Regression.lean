module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery.Example.Defs

open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery.Example

#guard observe == some {
  initialCandidates := [5]
  afterFirstCandidates := [6]
  consumerCuts := ([], [3])
  requests := [5, 6, 7]
  physicalCuts := [2, 3, 4]
  terminalOrigins := [3, 0, 4]
  fixedPoint := true
  beforeEdges := [(1, [3, 2, 7]), (2, [9])]
  afterEdges := [(1, [9, 5, 4, 3, 2, 7]), (2, [9])]
  beforePackets := [[3, 2, 3], [3, 2, 7], [3, 2, 11], [9]]
  afterPackets := [[9, 5, 4, 3, 2, 3], [9, 5, 4, 3, 2, 7], [9, 5, 4, 3, 2, 11], [9]]
  beforeRuns := [none, none, some 9]
  afterRuns := [none, none, some 9]
}

#guard stopCases == some (true, true)
