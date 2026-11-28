module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Example.Defs

open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Example

#guard observe == some {
  beforeConsumerCuts := []
  afterConsumerCuts := [3]
  consumerOperandCuts := [(0, 3), (0, 0)]
  selections := [(0, 2), (0, 3)]
  consumerIndices := (4, 3)
  savedCounts := [2, 3, 4]
  physicalSlots := [some 1, some 0]
  beforeEdges := [(1, [3, 2, 7]), (2, [9])]
  afterEdges := [(1, [5, 4, 3, 2, 7]), (2, [9])]
  beforePackets := [[3, 2, 3], [3, 2, 7], [3, 2, 11], [9]]
  afterPackets := [[5, 4, 3, 2, 3], [5, 4, 3, 2, 7], [5, 4, 3, 2, 11], [9]]
  beforeRuns := [none, none, some 9]
  afterRuns := [none, none, some 9]
}

#guard mixed == some {
  headerOrder := [3, 0, 5, 6, 7, 4]
  selections := [(1, 5), (0, 2)]
  secondIndex := 2
  finalRuns := [none, none, some 9]
}

#guard refused == some { position := 8, request := ⟨5, 3⟩ }
