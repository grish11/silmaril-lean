module

public import Silmaril.SSA.RVSDG.Theta.Defs
import Silmaril.Proofs.SSA.RVSDG.Theta.Operational

public section

namespace Silmaril.SSA.RVSDG.Theta

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {carried : Ports (PortType V S)} {sigs : List (Ports (PortType V S))}

theorem Term.toTerm_toGraph (term : Term Op carried sigs) : term.toGraph.toTerm = term :=
  congrArg Term.mk (RVSDG.Term.toTerm_toGraph term.body)

theorem Graph.toGraph_toTerm (graph : Graph Op carried sigs) : graph.toTerm.toGraph = graph :=
  congrArg Graph.mk (RVSDG.Graph.toGraph_toTerm graph.body)

/-- Converting the θ body's representation preserves and reflects finite return. -/
theorem Term.returns_toGraph (term : Term Op carried sigs) (m : Model.{u, v, w} Op)
    (input output : Tuple m.Val carried) :
    term.toGraph.Returns m input output ↔ term.Returns m input output :=
  Proofs.returns_toGraph term m input output

/-- A finite return and an infinite sequence of successful restarts are exclusive. -/
theorem Graph.not_diverges_of_returns (graph : Graph Op carried sigs) (m : Model.{u, v, w} Op)
    {input output : Tuple m.Val carried} (execution : graph.Returns m input output) :
    ¬ graph.Diverges m input :=
  Proofs.not_diverges_of_returns graph m execution

end Silmaril.SSA.RVSDG.Theta
