module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Example.Defs

open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Example

#guard observe == some {
  headerBindings := (6, 5)
  exitBindings := (0, 1)
  beforeEdges := [[3, 2, 7], [9]]
  afterEdges := [[3, 2, 7], [5, 4]]
  exactPackets := true
  beforeRuns := [none, none, none, some 9]
  afterRuns := [none, none, none, some 9]
}

#guard refusesFeedback == some (true, true)
