module

public import Silmaril.SSA.RVSDG.Theta.Petri.Defs
import Silmaril.Proofs.SSA.RVSDG.Theta.Petri

public section

namespace Silmaril.SSA.RVSDG.Theta.Petri

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {carried : Ports (PortType V S)} {sigs : List (Ports (PortType V S))}

/-- Every finite Petri return corresponds to a finite θ return, and conversely. -/
theorem finishes_iff (m : Model.{u, v, w} Op) (graph : Graph Op carried sigs)
    (input output : Tuple m.Val carried) :
    Finishes m graph input output ↔ graph.Returns m input output :=
  ⟨Proofs.sound m graph, Proofs.complete m graph⟩

/-- Restart divergence agrees with the infinite-iteration observation. -/
theorem diverges_iff (m : Model.{u, v, w} Op) (graph : Graph Op carried sigs)
    (input : Tuple m.Val carried) : Diverges m graph input ↔ graph.Diverges m input :=
  Proofs.diverges_iff m graph input

/-- A completed continuing body can make a real restart step to a fresh marking. -/
theorem restart_after_body (m : Model.{u, v, w} Op) (graph : Graph Op carried sigs)
    {input next : Tuple m.Val carried}
    (returns : RVSDG.Petri.Finishes m graph.body input (bodyResult m true next)) :
    ∃ mark, Relation.ReflTransGen (Step m graph) (initial m graph input) mark ∧
      Step m graph mark (initial m graph next) :=
  Proofs.restart_after_body m graph returns

end Silmaril.SSA.RVSDG.Theta.Petri
