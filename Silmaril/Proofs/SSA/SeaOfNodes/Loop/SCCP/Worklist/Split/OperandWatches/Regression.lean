module

import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.OperandWatches.Example.Defs
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.OperandWatches.Thms
meta import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.OperandWatches.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.OperandWatches

open SCCP.Example.Bank (model facts)
open Phi.Support.Example (graph)
open OperandWatches.Example (watches skippedFlag resultReadsByte guardReadsByte exitActivation solveReport)

#guard skippedFlag == ([.control, .result], [])
#guard resultReadsByte == [.phi (0 : Fin 2), .phi (1 : Fin 2), .result]
#guard guardReadsByte == [.control, .phi (1 : Fin 2)]
#guard exitActivation == [.phi (1 : Fin 2), .result]
#guard solveReport = ([], true, false, (.constant true, .constant 255), .bottom)

example : (run model (facts true 255) watches).pending = [] := run_drains watches

example : solve model (facts true 255) watches = SCCP.solve model graph (facts true 255) :=
  solve_eq_simultaneous watches

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.OperandWatches
