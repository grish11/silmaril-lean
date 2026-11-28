module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Example.Defs

open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Example

#guard observe == some {
  retained := [3, 0, 4]
  moved := [5, 6, 7]
  headerBindings := 3
  exitBindings := 3
  exitOperandCuts := [[0, 0], [1, 0], [2, 1]]
  beforePackets := [[3, 2, 7], [9]]
  afterPackets := [[3, 2, 7], [7, 4, 1, 3, 2, 3, 2, 10, 1]]
  restoredPackets := [[3, 2, 7], [9]]
  beforeRuns := [none, none, none, some 9]
  afterRuns := [none, none, none, some 9]
}

#guard refusesRetainedRead == some (true, true)
#guard refusesGuard == some (true, true)
#guard refusesFeedback == some (true, true)
