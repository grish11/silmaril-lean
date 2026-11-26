module

public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Isomorphism.Defs
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.ExplicitRuntime.Isomorphism.Order

/-! # Topological position is fixed in checked one-token regions -/

public section

namespace Silmaril.SSA.RVSDG.NestedTheta

universe u v
variable {V S : Type u} {Op : Dialect.{u,v} V S}
variable {args outs : Ports (PortType V S)} {past sigs sigs' : List (Ports (PortType V S))}
variable {g : Graph Op args past sigs outs}

theorem Graph.ScopeChains.here (h : g.ScopeChains) : g.PredecessorChain := by
  cases g
  exact h.1

theorem Graph.ScopeChains.child (h : g.ScopeChains) (i : Fin sigs.length) (j : Fin (g.nodes i).kind.arity) :
    (g.children i j).ScopeChains := by
  cases g
  exact h.2 i j

variable {left : Graph Op args [] sigs outs} {right : Graph Op args [] sigs' outs}

/-- With a predecessor edge at every nonfirst vertex, preserving operand
addresses forces the vertex bijection to preserve each topological rank. -/
theorem Graph.PredecessorChain.numbering_fixed (chain : right.PredecessorChain)
    (ids : Fin sigs.length ≃ Fin sigs'.length)
    (inputs : ∀ i, (left.nodes i).inputs.addresses.map (Address.rename (renameVertex ids)) =
      (right.nodes (ids i)).inputs.addresses) (i : Fin sigs.length) : (ids i).val = i.val :=
  ExplicitRuntime.Isomorphism.Proofs.numbering_fixed ids inputs chain i

/-- In a chained scope the actual inputs must agree at the same numbering.
An argument address stays an argument under any vertex bijection. -/
theorem Graph.Isomorphic.inputs_at_rank (iso : Graph.Isomorphic Op left right)
    (chain : right.PredecessorChain) (i : Fin sigs.length) (j : Fin sigs'.length) (rank : i.val = j.val) :
    (left.nodes i).inputs.addresses = (right.nodes j).inputs.addresses :=
  ExplicitRuntime.Isomorphism.Proofs.addresses_at iso chain i j rank

namespace ExplicitRuntime

open OrderedRuntime.Structured (Data Threaded Ty Opcode)

variable {P E : Dialect.{u,v} V PUnit.{u+1}}
variable {args outs : Ports (Ty V)} {sigs : List (Ports (Ty V))}

/-- The one-live-token admission supplies a predecessor edge at every
nonfirst vertex, recursively through both γ and θ child tables. -/
theorem EntryChecked.scopeChains {a : Data args} {b : Data outs}
    {t : Term (Opcode P E) (Threaded args) [] sigs (Threaded outs)}
    (checked : EntryChecked (a := a) (b := b) t) : t.toGraph.ScopeChains :=
  Isomorphism.Proofs.scopeChains checked

end ExplicitRuntime
end Silmaril.SSA.RVSDG.NestedTheta
