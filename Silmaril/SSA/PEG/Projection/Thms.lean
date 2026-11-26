module

public import Silmaril.SSA.PEG.Projection.Defs
public import Silmaril.SSA.PEG.Semantics.Thms
import Silmaril.Proofs.SSA.PEG.Projection.Transport

public section

namespace Silmaril.SSA.PEG.Graph.Projection

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}
variable {g : Graph P params results n l} (p : g.Projection)

theorem embed_injective : Function.Injective p.rows.embed :=
  PEG.Projection.Proofs.embedding p

/-- Each operand occurrence maps to the original typed reference in that position. -/
theorem operand (i : Fin p.rows.length) (slot : Fin (p.graph.node i).inputs.length) :
    PEG.Projection.pushRef p.rows ((p.graph.node i).arg slot) = (g.node (p.rows.embed i)).arg slot :=
  PEG.Projection.Proofs.operand p i slot

theorem edge_iff (a b : Fin p.rows.length) (kind : EdgeKind (Fin l)) :
    p.graph.Edge a kind b ↔ g.Edge (p.rows.embed a) kind (p.rows.embed b) :=
  PEG.Projection.Proofs.edge p a b kind

theorem scoped_of (h : g.Scoped) : p.graph.Scoped :=
  PEG.Projection.Proofs.scoped_of p h

theorem demand_iff (q r : Request p.rows.length l) :
    p.graph.Demand q r ↔ g.Demand (p.request q) (p.request r) :=
  PEG.Projection.Proofs.demand p q r

/-- Every original demand of a retained request is also represented in
the projection, at the same iteration vector. -/
theorem predecessor {q : Request p.rows.length l} {r : Request n l}
    (h : g.Demand r (p.request q)) : ∃ s, p.request s = r ∧ p.graph.Demand s q :=
  PEG.Projection.Proofs.predecessor p h

theorem demandWellFounded (wf : WellFounded g.Demand) : WellFounded p.graph.Demand :=
  PEG.Projection.Proofs.demandWf p wf

/-- The rank restricts its vertex phases and retains every loop counter. -/
theorem rank_check (rank : DemandRank n l) (h : rank.check g = true) :
    (p.rank rank).check p.graph = true :=
  PEG.Projection.Proofs.rankCheck p rank h

variable (m : Interpretation.{u,v,w} P) (env : Tuple m.Value params)

theorem equation (values : g.Valuation m) (q : Request p.rows.length l) :
    p.graph.equation m env (p.valuation m values) q = g.equation m env values (p.request q) :=
  PEG.Projection.Proofs.equation p m env values q

/-- Any solution of the original equations restricts to a solution, even
when existence or uniqueness on the larger graph is given separately. -/
theorem solves {values : g.Valuation m} (h : g.Solves m env values) :
    p.graph.Solves m env (p.valuation m values) :=
  PEG.Projection.Proofs.solves p m env h

theorem denote (wf : WellFounded g.Demand) (localWf : WellFounded p.graph.Demand) :
    p.graph.denote m env localWf = p.valuation m (g.denote m env wf) :=
  PEG.Projection.Proofs.denote p m env wf localWf

/-- Exact Figure 11 agreement, including bottom, at the designated root
tuple and the original iteration vector. -/
theorem observe_denote (wf : WellFounded g.Demand) (localWf : WellFounded p.graph.Demand) (i : Index l) :
    p.graph.observe m (p.graph.denote m env localWf) i = g.observe m (g.denote m env wf) i :=
  PEG.Projection.Proofs.observe p m env wf localWf i

end Silmaril.SSA.PEG.Graph.Projection
