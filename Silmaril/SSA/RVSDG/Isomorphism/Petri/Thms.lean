module

public import Silmaril.SSA.RVSDG.Isomorphism.Thms
public import Silmaril.SSA.RVSDG.Petri.Thms

public section

namespace Silmaril.SSA.RVSDG

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args outs : Ports (PortType V S)} {sigs sigs' : List (Ports (PortType V S))}

/-- Isomorphic graphs have the same finite Petri completion observations. -/
theorem Graph.Isomorphic.finishes_iff
    {left : Graph Op args [] sigs outs} {right : Graph Op args [] sigs' outs}
    (iso : Graph.Isomorphic Op left right) (m : Model.{u, v, w} Op)
    (entry : Tuple m.Val args) (output : Tuple m.Val outs) :
    Petri.Finishes m left entry output ↔ Petri.Finishes m right entry output := by
  rw [Petri.finishes_iff, Petri.finishes_iff, iso.run_eq m entry]

end Silmaril.SSA.RVSDG
