module

public import Silmaril.SSA.RVSDG.Isomorphism.Defs
import Silmaril.Proofs.SSA.RVSDG.Isomorphism.Invariance

/-! Typed hierarchical graph isomorphism preserves numbered evaluation. -/

public section

namespace Silmaril.SSA.RVSDG

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args outs : Ports (PortType V S)} {sigs sigs' : List (Ports (PortType V S))}

/-- A typed hierarchical port-graph isomorphism preserves the returned tuple,
including any returned state, for every total deterministic primitive model. -/
theorem Graph.Isomorphic.run_eq
    {left : Graph Op args [] sigs outs} {right : Graph Op args [] sigs' outs}
    (iso : Graph.Isomorphic Op left right) (m : Model.{u, v, w} Op) (entry : Tuple m.Val args) :
    left.run m entry = right.run m entry :=
  Isomorphism.Proofs.run_eq iso m entry

end Silmaril.SSA.RVSDG
