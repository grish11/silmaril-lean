module

import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index.Example.Defs
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index.Thms
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Support.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Support.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index

open SCCP.Example.Bank (model graph facts)
open Index.Example (index readerReport before flagOnly multiTrigger prequeued gated activation
  activationAndFields solveReport)

#guard readerReport == [[1], [0, 1]]
#guard flagOnly == [.control, .phi 1, .result]
#guard multiTrigger == [.control, .phi 0, .phi 1, .result]
#guard prequeued == [.phi 1, .control, .phi 0, .result]
#guard gated == [.control, .result]
#guard activation == [.phi 0, .phi 1]
#guard activationAndFields == [.result, .phi 0, .control, .phi 1]
#guard solveReport = (true, true, (.overdefined, .overdefined), .overdefined)

-- The Boolean feedback reads the byte through two producers. The byte also feeds back directly.
private def transitive := build Phi.Support.Example.graph
#guard wake model transitive Phi.Support.Example.before Phi.Support.Example.changedFlag [] == [.control]
#guard wake model transitive Phi.Support.Example.before Phi.Support.Example.changedByte [] ==
  [.control, .phi (0 : Fin 2), .phi (1 : Fin 2)]

example : step model (facts false 0) index (.phi (0 : Fin 2)) before [.phi (1 : Fin 2)] =
    Split.step model (graph true) (facts false 0) (.phi (0 : Fin 2)) before [.phi (1 : Fin 2)] :=
  step_eq index _ _ _

example : (run model (facts false 0) index).pending = [] := run_drains index

example : solve model (facts false 0) index = SCCP.solve model (graph true) (facts false 0) :=
  solve_eq_simultaneous index

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index
