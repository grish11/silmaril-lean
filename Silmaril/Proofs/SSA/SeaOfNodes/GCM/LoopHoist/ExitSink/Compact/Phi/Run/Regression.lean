module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Run.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Run.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Run.Example.Defs

open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Run.Example

#guard immediate == some {
  feedbacks := 0
  taken := "false"
  remaining := 1
  projection := [4, 6, 8]
  compactReads := [4, 6, 8]
  fullPacket := [9, 6, 0, 3, 2, 5, 4, 1, 1]
  compactPacket := [2, 4, 1]
  latch := [2, 4, 1]
  output := 13
}

#guard afterFeedback == some {
  feedbacks := 2
  taken := "false"
  remaining := 1
  projection := [4, 6, 8]
  compactReads := [4, 6, 8]
  fullPacket := [15, 12, 0, 3, 2, 11, 2, 10, 1]
  compactPacket := [2, 2, 1]
  latch := [2, 2, 1]
  output := 9
}

#guard exhausted.isNone
#guard arrivedWithoutReturn == some (2, 0, true)

#guard parallel 1 == some ⟨0, "true", 1, [0], [0], [7, 9], [7], [7], 7⟩
#guard parallel 0 == some ⟨0, "false", 1, [0], [1], [9, 7], [9], [9], 9⟩
