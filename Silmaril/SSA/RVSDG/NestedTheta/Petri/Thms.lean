module

public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Defs
import Silmaril.SSA.RVSDG.NestedTheta.Thms
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Petri.Soundness
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Petri.Completeness

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Petri

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args outs : Ports (PortType V S)} {sigs : List (Ports (PortType V S))}

/-- Every finite completed firing trace has an unbounded term derivation
with the same full output tuple. Every such derivation admits a finite trace. -/
theorem finishes_toTerm (m : Model.{u, v, w} Op) (graph : Graph Op args [] sigs outs)
    (input : Tuple m.Val args) (output : Tuple m.Val outs) :
    Finishes m graph input output ↔ graph.toTerm.Returns m input output :=
  ⟨Proofs.sound m graph input output, Proofs.complete m graph input output⟩

/-- Firing and the numbered graph evaluator have the same finite return observations. -/
theorem finishes_iff (m : Model.{u, v, w} Op) (graph : Graph Op args [] sigs outs)
    (input : Tuple m.Val args) (output : Tuple m.Val outs) :
    Finishes m graph input output ↔ graph.Returns m input output :=
  (finishes_toTerm m graph input output).trans (graph.returns_iff m input output).symm

end Silmaril.SSA.RVSDG.NestedTheta.Petri
