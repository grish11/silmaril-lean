module

import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Example.Defs
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Thms
meta import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split

open SCCP.Example.Bank (facts graph model observe)
open Split.Example (direct report wideningWake enableExitWake)

example : (report direct true 0).2 =
    (true, false, (.constant true, .constant 0), .bottom) := rfl

example : (report direct true 0).1 =
    [.control, .control, .phi 0, .phi 1, .control, .phi 0, .phi 1] := rfl

#guard (report (graph false) true 0).2 =
    (true, true, (.constant true, .overdefined), .overdefined)

example : wideningWake [] = [.control, .phi 1] := rfl
example : wideningWake [.phi 1] = [.phi 1, .control] := rfl
example : enableExitWake = [.result] := rfl

#guard (report (graph true) false 0).2 =
    (true, true, (.overdefined, .overdefined), .overdefined)

-- The second pop sees the flag published by the first one.
#guard observe (runSteps model (graph true) (facts false 0) 2 Phi.Example.crossSnapshot
    [.phi (0 : Fin 2), .phi (1 : Fin 2)]).state.2.1 = (.constant true, .constant 1)

example : report (graph false) true 5 =
    ([.control, .control, .phi 0, .phi 1, .control, .result],
      false, true, (.constant true, .constant 5), .constant 6) := rfl

example : (run model (graph true) (facts false 0)).pending = [] :=
  run_drains model (graph true) (facts false 0)

example : solve model (graph true) (facts false 0) = SCCP.solve model (graph true) (facts false 0) :=
  solve_eq_simultaneous model (graph true) (facts false 0)

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split
