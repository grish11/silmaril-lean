module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Example.Defs

open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Example
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Example (input)

#guard observe == some {
  selectedSlots := [4, 6, 8]
  firstProducerReads := [6, 4]
  fullPackets := [[3, 2, 7], [7, 4, 1, 3, 2, 3, 2, 10, 1]]
  compactPackets := [[3, 2, 7], [2, 2, 1]]
  projectedPackets := [[3, 2, 7], [2, 2, 1]]
  fullExitBindings := 3
  compactExitBindings := 3
  fullRuns := [none, none, none, some 9]
  compactRuns := [none, none, none, some 9]
}

-- Distinct values distinguish the packet order from the first producer's reads.
#guard (observeOn (input 4 11 1)).map Observation.compactPackets == some [[3, 2, 9], [2, 4, 1]]

#guard refusesMissingOperand == some true
#guard prunesDeadRead == some ([4, 6, 8], 4, 3)
