module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Example.Defs

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Regression

open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Example

#guard observe == some {
  logicalCuts := [4, 3]
  physicalCuts := [3, 2]
  slots := [some 1, some 2, some 3, some 0, some 4]
  physicalSaves := [3, 9, 5, 4, 2]
  packets := [[9, 5, 4, 3, 2, 3], [9, 5, 4, 3, 2, 7], [9, 5, 4, 3, 2, 11], [9]]
  exitOccurrence := true
  runs := [none, none, some 9]
  appendRuns := [none, none, some 9] }
#guard refusal ⟨7, 2⟩ == some (.nomination 4 ⟨7, 2⟩ .rejected)
#guard refusal ⟨6, 3⟩ == some (.nomination 4 ⟨6, 3⟩ .rejected)

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Regression
