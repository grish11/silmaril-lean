module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Discovery.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Discovery.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Discovery.Example.Defs

open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Discovery.Example

#guard observe == some {
  directOrigins := [3, 4]
  required := [3, 0, 4]
  moved := [5, 6, 7]
  mask := [false, true, false, true, false, true]
  originalPackets := [[3, 2, 7], [9]]
  restoredPackets := [[3, 2, 7], [9]]
  originalRuns := [none, none, none, some 9]
  emittedRuns := [none, none, none, some 9]
}

#guard noMove == some ([false, false], true)
#guard exitRefusal == some ([false, false, true, false, true, false], true)
