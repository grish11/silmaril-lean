module

public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Defs

/-! Each local vertex number in a checked token chain is its execution rank. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta

universe u v
variable {V S : Type u} {Op : Dialect.{u,v} V S}
variable {args outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

/-- Every vertex after the first has an operand from its immediate predecessor. -/
def Graph.PredecessorChain (g : Graph Op args past sigs outs) : Prop :=
  ∀ i : Fin sigs.length, 0 < past.length + i.val →
    ∃ port, Address.output (past.length + i.val - 1) port ∈ (g.nodes i).inputs.addresses

/-- The predecessor dependency holds in this region and in each child scope. -/
def Graph.ScopeChains : {args outs : Ports (PortType V S)} →
    {past sigs : List (Ports (PortType V S))} → Graph Op args past sigs outs → Prop
  | _, _, _, _, .region nodes children results =>
    (Graph.region nodes children results).PredecessorChain ∧ ∀ i j, (children i j).ScopeChains

end Silmaril.SSA.RVSDG.NestedTheta
