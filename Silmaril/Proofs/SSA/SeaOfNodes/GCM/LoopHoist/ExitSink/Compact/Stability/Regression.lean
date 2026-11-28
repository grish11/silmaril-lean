module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability.Example.Defs

open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability.Example

#guard observe == some {
  firstProjection := [4, 6, 8]
  secondInputs := [2, 1, 0]
  secondMask := [false, false, false]
  secondProjection := [0, 1, 2]
  firstReads := [[1, 0], [0, 3], [0, 1], [0]]
  secondReads := [[1, 0], [0, 3], [0, 1], [0]]
  firstPackets := [[3, 2, 9], [2, 4, 1]]
  secondPackets := [[3, 2, 9], [2, 4, 1]]
}

#guard ambientOnly == some ([], [0], [], [[7, 7], []])
