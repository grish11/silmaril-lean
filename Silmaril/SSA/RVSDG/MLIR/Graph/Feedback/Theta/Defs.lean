module

public import Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.Defs
public import Silmaril.SSA.RVSDG.Theta.Institution.Defs

/-! # Embed a data-only numbered θ into the scoped feedback bridge -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.WholeTheta

open NestedTheta.Institution

universe u v w
variable {V : Type u} {A : Stateless.Signature.{u,v} V}
variable {carried : Ports (PortSort V)} {sigs : List (Ports (PortSort V))}

/-- Wrap each body opcode as pure, then place the original numbered body
inside one θ binding with positional input and result wiring. -/
def embed (g : Theta.Graph A.pure carried sigs) : NestedTheta.Graph A.op carried [] [carried] carried :=
  (NestedTheta.Term.ofTheta (Theta.Institution.relabel .pure g).toTerm).toGraph

/-- View a stateless model as a total model of the source primitive alphabet. -/
abbrev runtime (m : Stateless.Model.{u,v,w} A) : Model.{u,v,max u w} A.pure :=
  ⟨m.value, fun _ => PUnit, fun op => m.run op⟩

end Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.WholeTheta
