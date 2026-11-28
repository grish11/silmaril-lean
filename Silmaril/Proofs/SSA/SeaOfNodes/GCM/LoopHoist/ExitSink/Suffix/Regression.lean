module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Suffix.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Suffix.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Suffix.Example.Defs

open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Suffix.Example

#guard observe == some {
  split := 3
  exitBindings := 3
  shorterAccepted := true
  earlierRefused := true
  exitOperandCuts := [[0, 0], [1, 0], [2, 1]]
  beforePackets := [[3, 2, 7], [9]]
  afterPackets := [[3, 2, 7], [7, 4, 1, 3, 2, 3, 2, 10, 1]]
  restoredPackets := [[3, 2, 7], [9]]
  beforeRuns := [none, none, none, some 9]
  afterRuns := [none, none, none, some 9]
}

#guard retainsFeedbackProducer == some (5, 1, true)
#guard refusesFeedbackResult == some true
