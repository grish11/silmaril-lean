module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Example.Defs

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Regression

open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Example

#guard observe == some {
  physicalIndex := 1
  physicalSaves := [3, 4, 2]
  packets := [[4, 3, 2, 3], [4, 3, 2, 7], [4, 3, 2, 11], [4]]
  readsExitOccurrence := true
  runs := [none, none, some 4]
  appendRuns := [none, none, some 4] }
#guard beforeBoth == some (2, [3, 2, 5])
#guard refused == [true, true, true, true]

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Regression
