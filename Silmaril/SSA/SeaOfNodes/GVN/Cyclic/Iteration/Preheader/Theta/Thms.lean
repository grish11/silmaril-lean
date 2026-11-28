module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.Theta.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.Theta.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.Theta

open Activation (Inputs)
open Builder.Preheader (Native)
open Diamond (Ty ValueSort sortValue)
open Loop (thetaRuntime)
open Pure.SubZero (model)
open RVSDG.NestedTheta (MonadicModel)

variable {inputs carried : List (ValueSort Unit)} {entrySigs headerSigs : List (List (Ty Unit))}
variable {out : ValueSort Unit}
variable (loop : Native inputs carried entrySigs headerSigs out) (input : Inputs model inputs)

/-- The emitted preheader and θ entry keep their typed labels and all
ordered input addresses, including the full entry Phi packet. -/
theorem emit_entry :
    entryPrefix (emit loop) = entryPrefix loop.lowerTheta :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.Theta.emit_entry loop

/-- The two numbered graphs return the same singleton value tuple.
Each graph uses its own finite execution bound. -/
theorem emit_returns_iff (value : sortValue model.value out) :
    (emit loop).Returns (thetaRuntime model) input (.cons value .nil) ↔
      loop.lowerTheta.Returns (thetaRuntime model) input (.cons value .nil) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.Theta.emit_returns_iff loop input value

/-- The existing partial denotation observes the same value or absence
from the same original typed input tuple. -/
theorem emit_observe :
    RVSDG.NestedTheta.Partial.observe (MonadicModel.ofRuntime (thetaRuntime model)) (emit loop) input =
      RVSDG.NestedTheta.Partial.observe (MonadicModel.ofRuntime (thetaRuntime model)) loop.lowerTheta input :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.Theta.emit_observe loop input

theorem emit_absent_iff :
    RVSDG.NestedTheta.Partial.observe (MonadicModel.ofRuntime (thetaRuntime model)) (emit loop) input = Part.none ↔
      RVSDG.NestedTheta.Partial.observe (MonadicModel.ofRuntime (thetaRuntime model)) loop.lowerTheta input = Part.none := by
  rw [emit_observe loop input]

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.Theta
