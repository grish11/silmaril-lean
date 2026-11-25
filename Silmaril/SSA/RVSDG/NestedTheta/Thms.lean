module

public import Silmaril.SSA.RVSDG.NestedTheta.Defs
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Correspondence
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Embeddings

public section

namespace Silmaril.SSA.RVSDG.NestedTheta

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

theorem Term.toTerm_toGraph (t : Term Op args past sigs outs) : t.toGraph.toTerm = t :=
  Proofs.toTerm_toGraph t

theorem Graph.toGraph_toTerm (g : Graph Op args past sigs outs) : g.toTerm.toGraph = g :=
  Proofs.toGraph_toTerm g

theorem Graph.run_toTerm (g : Graph Op args [] sigs outs) (m : Model.{u, v, w} Op)
    (fuel : Nat) (input : Tuple m.Val args) : g.toTerm.run m fuel input = g.run m fuel input :=
  Proofs.eval_toTerm g m fuel input PUnit.unit

/-- Every successful bounded graph run gives an unbounded finite execution derivation.
Every such derivation has a sufficient bound that works for all larger bounds. -/
theorem Graph.returns_iff (g : Graph Op args [] sigs outs) (m : Model.{u, v, w} Op)
    (input : Tuple m.Val args) (output : Tuple m.Val outs) :
    g.Returns m input output ↔ g.toTerm.Returns m input output :=
  Proofs.returns_iff g m input output

theorem Graph.returns_eventually (g : Graph Op args [] sigs outs) (m : Model.{u, v, w} Op)
    (input : Tuple m.Val args) (output : Tuple m.Val outs) (h : g.Returns m input output) :
    ∃ limit, ∀ fuel, limit ≤ fuel → g.run m fuel input = some output :=
  Proofs.returns_eventually g m input output h

theorem Term.returns_toGraph (t : Term Op args [] sigs outs) (m : Model.{u, v, w} Op)
    (input : Tuple m.Val args) (output : Tuple m.Val outs) :
    t.toGraph.Returns m input output ↔ t.Returns m input output := by
  rw [Graph.returns_iff, Term.toTerm_toGraph]

theorem Term.run_ofBase (t : RVSDG.Term Op args [] sigs outs) (m : Model.{u, v, w} Op)
    (fuel : Nat) (input : Tuple m.Val args) :
    (Term.ofBase t).run m fuel input = some (t.run m input) :=
  Proofs.term_eval_ofBase m fuel t input PUnit.unit

theorem Graph.run_ofBase (g : RVSDG.Graph Op args [] sigs outs) (m : Model.{u, v, w} Op)
    (fuel : Nat) (input : Tuple m.Val args) :
    (Graph.ofBase g).run m fuel input = some (g.run m input) :=
  Proofs.graph_eval_ofBase m fuel g input PUnit.unit

theorem Term.returns_ofTheta (t : Theta.Term Op args sigs) (m : Model.{u, v, w} Op)
    (input output : Tuple m.Val args) :
    (Term.ofTheta t).Returns m input output ↔ t.Returns m input output :=
  Proofs.term_returns_ofTheta m t input output

theorem Graph.returns_ofTheta (g : Theta.Graph Op args sigs) (m : Model.{u, v, w} Op)
    (input output : Tuple m.Val args) :
    (Graph.ofTheta g).Returns m input output ↔ g.Returns m input output :=
  Proofs.graph_returns_ofTheta m g input output

end Silmaril.SSA.RVSDG.NestedTheta
