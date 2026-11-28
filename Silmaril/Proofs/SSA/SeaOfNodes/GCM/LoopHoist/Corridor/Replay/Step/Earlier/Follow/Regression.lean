module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow.Example.Defs

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow.Regression

open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow.Example

#guard observe == some {
  logicalOperandCuts := [3, 0]
  physicalOperandCuts := [2, 0]
  onFalseExitUse := true
  physicalSaves := [3, 5, 4, 2]
  packets := [[5, 4, 3, 2, 3], [5, 4, 3, 2, 7], [5, 4, 3, 2, 11], [5]]
  runs := [none, none, some 5]
  appendRuns := [none, none, some 5] }
#guard refused == [true, true, true]

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow.Regression
