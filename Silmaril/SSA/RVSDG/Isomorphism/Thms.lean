module

public import Silmaril.SSA.RVSDG.Isomorphism.Defs
import Silmaril.Proofs.SSA.RVSDG.Isomorphism.Invariance

/-! Typed hierarchical graph isomorphism preserves numbered evaluation. -/

public section

namespace Silmaril.SSA.RVSDG

universe u v w

theorem Wires.output_before {Ty : Type u} {args users : Ports Ty} {past : List (Ports Ty)}
    (wires : Wires args past users) {vertex port : Nat}
    (mem : Address.output vertex port ∈ wires.addresses) : vertex < past.length :=
  Isomorphism.Proofs.source_before wires mem

theorem site_prefix_length {Ty : Type u} (past sigs : List (Ports Ty)) (i : Fin sigs.length) :
    (site past sigs i).1.length = past.length + i.val :=
  Isomorphism.Proofs.site_length past sigs i

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
