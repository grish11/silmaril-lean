module

import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Support.Example.Defs
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Support.Thms
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Thms
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Thms
meta import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Support.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Support

open SCCP.Example.Bank (facts fields model)
open Support.Example (graph before changedFlag changedByte flagSupport wakeAfterFlag wakeAfterByte solveReport)

private theorem supported : feedbackSupport graph (0 : Fin 2) = {(1 : Fin 2)} := by decide
example : flagSupport = [1] := rfl

-- Only control watches the unrelated flag change.
#guard wakeAfterFlag = [.control]

-- The producer-fed flag and the direct byte both watch the changed byte.
example : wakeAfterByte = [.control, .phi 0, .phi 1] := rfl

example : Phi.dependencies model graph (facts true 255) before (0 : Fin 2) =
    Phi.dependencies model graph (facts true 255) changedFlag (0 : Fin 2) := by
  let support := feedbackSupport graph (0 : Fin 2)
  have masked : restrictBank support before.2.1 = restrictBank support changedFlag.2.1 := by
    apply (restrictBank_eq_iff support).mpr
    intro i member
    change i ∈ feedbackSupport graph (0 : Fin 2) at member
    rw [supported, Finset.mem_singleton] at member
    subst i
    rfl
  exact congrArg (fun bank => ((true, some (.inr bank)) : Watched model.value fields (0 : Fin 2))) masked

example : (headerFacts model graph (facts true 255) before.2.1).feedback (0 : Fin 2) = .constant ⟨true⟩ :=
  rfl

example : (headerFacts model graph (facts true 255) changedByte.2.1).feedback (0 : Fin 2) = .overdefined :=
  rfl

#guard solveReport = (true, false, (.constant true, .constant 255), .bottom)

example : Split.solve model graph (facts true 255) = SCCP.solve model graph (facts true 255) :=
  Split.solve_eq_simultaneous model graph (facts true 255)

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Support
