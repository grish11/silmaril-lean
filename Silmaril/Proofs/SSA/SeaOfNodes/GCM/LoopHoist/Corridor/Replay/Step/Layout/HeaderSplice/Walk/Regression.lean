module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.Example.Defs

open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.Example

#guard observe == some {
  indices := [1, 2, 3]
  orders := [[3, 5, 0, 4, 6, 7], [3, 0, 5, 4, 6, 7], [3, 0, 4, 5, 6, 7]]
  blocked := true
  blockedCut := 5
  operandCuts := [(0, 0), (0, 1)]
  ordinaryReads := [4, 5]
  falseExitRead := true
  beforeEdges := [(1, [3, 2, 7]), (2, [4])]
  afterEdges := [(1, [3, 2, 7]), (2, [4])]
  beforePackets := [[3, 2, 3], [3, 2, 7], [3, 2, 11], [4]]
  afterPackets := [[3, 2, 3], [3, 2, 7], [3, 2, 11], [4]]
  beforeRuns := [none, none, some 4]
  afterRuns := [none, none, some 4]
}

#guard limited == some ([1, 2], false, true)
#guard ranking == some ((0, 1), (1, 3), (0, 1), [none, none, some 4], [none, none, some 4])
