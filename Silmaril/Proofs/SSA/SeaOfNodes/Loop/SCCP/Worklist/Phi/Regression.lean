module

import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Example.Defs
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Thms

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi

open SCCP.Example.Bank (model graph facts observe)
open Phi.Example (beforeWidening crossSnapshot widening feedbackReads)

example : widening [] = ((.constant true, .overdefined), [1]) := rfl
example : widening [(1 : Fin 2)] = ((.constant true, .overdefined), [1]) := rfl

private def afterWord := update model (graph false) (facts true 0) (1 : Fin 2) beforeWidening

example : dependencies model (graph false) (facts true 0) afterWord (0 : Fin 2) =
    dependencies model (graph false) (facts true 0) beforeWidening (0 : Fin 2) := rfl

example : dependencies model (graph false) (facts true 0) afterWord (1 : Fin 2) ≠
    dependencies model (graph false) (facts true 0) beforeWidening (1 : Fin 2) := by decide

example : feedbackReads = ((.constant true, .constant 0), (.constant true, .constant 1)) := rfl

example : feedbackReads.1 =
    observe (SCCP.transfer model (graph true) (facts false 0) crossSnapshot).2.1 := rfl

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi
