module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Example.Defs

open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Example

#guard observe == some {
  bindingAndCuts := (3, 2, 2)
  beforeOrigins := [3, 0, 4, 5, 6, 7]
  afterOrigins := [3, 0, 5, 4, 6, 7]
  ordinaryReads := [4, 5]
  falseExitRead := true
  beforeEdges := [(1, [3, 2, 7]), (2, [4])]
  afterEdges := [(1, [3, 2, 7]), (2, [4])]
  beforePackets := [[3, 2, 3], [3, 2, 7], [3, 2, 11], [4]]
  afterPackets := [[3, 2, 3], [3, 2, 7], [3, 2, 11], [4]]
  beforeRuns := [none, none, some 4]
  afterRuns := [none, none, some 4]
}

#guard refused == some (true, true)

#guard ranking == some {
  depths := (0, 1)
  headerCut := 4
  headerInsertion := 3
  outsideBeforeProducer := true
  lateSelection := (1, 4)
  depthSelection := (0, 1)
  lateRuns := [none, none, some 4]
  depthRuns := [none, none, some 4]
}
