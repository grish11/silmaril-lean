module

public import Silmaril.SSA.PEG.Semantics.Reindex.Defs
public import Silmaril.SSA.PEG.Semantics.Thms
public import Silmaril.SSA.PEG.Reindex.Thms
import Silmaril.Proofs.SSA.PEG.Semantics.Reindex.Demand
import Silmaril.Proofs.SSA.PEG.Semantics.Reindex.Rank
import Silmaril.Proofs.SSA.PEG.Semantics.Reindex.Observation

public section

namespace Silmaril.SSA.PEG

open RVSDG (Tuple)

universe u v w

variable {n n' l l' : Nat}
variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)}

theorem Index.reindex_inverse (i : Index l) (loops : Fin l' ≃ Fin l) :
    (i.reindex loops).reindex loops.symm = i :=
  Semantics.Reindex.Proofs.index_inverse i loops

theorem Index.reindex_set (i : Index l) (loops : Fin l' ≃ Fin l) (key : Fin l) (k : Nat) :
    (i.set key k).reindex loops = (i.reindex loops).set (loops.symm key) k :=
  Semantics.Reindex.Proofs.index_set i loops key k

theorem EdgeKind.changes_reindex (loops : Fin l' ≃ Fin l) (kind : EdgeKind (Fin l')) (i j : Index l') :
    kind.Changes i j ↔ (kind.map loops).Changes (i.reindex loops.symm) (j.reindex loops.symm) :=
  Semantics.Reindex.Proofs.changes loops kind i j

theorem RankComponent.value_reindex (c : RankComponent n l)
    (rows : Fin n' ≃ Fin n) (loops : Fin l' ≃ Fin l) (q : Request n' l') :
    (c.reindex rows loops).value q = c.value (Request.toOriginal rows loops q) := by
  cases c <;> rfl

variable (g : Graph P params results n l) (rows : Fin n' ≃ Fin n) (loops : Fin l' ≃ Fin l)

theorem Graph.demand_reindex (p q : Request n' l') :
    (g.reindex rows loops).Demand p q ↔
      g.Demand (Request.toOriginal rows loops p) (Request.toOriginal rows loops q) :=
  Semantics.Reindex.Proofs.demand g rows loops p q

theorem Graph.demandWellFounded_reindex :
    WellFounded (g.reindex rows loops).Demand ↔ WellFounded g.Demand :=
  Semantics.Reindex.Proofs.demand_wf g rows loops

/-- The same rank certificate checks after transporting both the vertex
phases and the loop counters. -/
theorem Graph.rank_check_reindex (rank : DemandRank n l) :
    (rank.reindex rows loops).check (g.reindex rows loops) = rank.check g :=
  Semantics.Reindex.Proofs.rank_check g rank rows loops

variable (m : Interpretation.{u,v,w} P) (env : Tuple m.Value params)

theorem Graph.equation_reindex (values : g.Valuation m) (q : Request n' l') :
    (g.reindex rows loops).equation m env (g.reindexValuation m rows loops values) q =
      g.equation m env values (Request.toOriginal rows loops q) :=
  Semantics.Reindex.Proofs.equation env rows loops values q

/-- Figure 11 denotation agrees at every transported request, including bottom. -/
theorem Graph.denote_reindex (wf : WellFounded g.Demand)
    (mapped : WellFounded (g.reindex rows loops).Demand) :
    (g.reindex rows loops).denote m env mapped = g.reindexValuation m rows loops (g.denote m env wf) :=
  Semantics.Reindex.Proofs.denote env rows loops wf mapped

/-- Coherent row and loop permutations preserve all designated observations
in their original order, at the corresponding iteration coordinates. -/
theorem Graph.observe_denote_reindex (wf : WellFounded g.Demand)
    (mapped : WellFounded (g.reindex rows loops).Demand) (i : Index l') :
    (g.reindex rows loops).observe m ((g.reindex rows loops).denote m env mapped) i =
      g.observe m (g.denote m env wf) (i.reindex loops.symm) :=
  Semantics.Reindex.Proofs.observe env rows loops wf mapped i

variable {g rows loops m env} {new : Graph P params results n' l'}

theorem Graph.ReindexCertificate.demandWellFounded_iff [DecidableEq Data]
    (cert : g.ReindexCertificate new rows loops) : WellFounded new.Demand ↔ WellFounded g.Demand :=
  cert.graph_eq ▸ g.demandWellFounded_reindex rows loops

theorem Graph.ReindexCertificate.rank_check [DecidableEq Data]
    (cert : g.ReindexCertificate new rows loops) (rank : DemandRank n l) :
    (rank.reindex rows loops).check new = rank.check g :=
  cert.graph_eq ▸ g.rank_check_reindex rows loops rank

/-- Observation transport for an independently supplied, checked graph table. -/
theorem Graph.ReindexCertificate.observe_denote [DecidableEq Data]
    (cert : g.ReindexCertificate new rows loops) (m : Interpretation.{u,v,w} P)
    (env : Tuple m.Value params) (wf : WellFounded g.Demand) (newWF : WellFounded new.Demand)
    (i : Index l') :
    new.observe m (new.denote m env newWF) i =
      g.observe m (g.denote m env wf) (i.reindex loops.symm) := by
  have same := cert.graph_eq
  subst new
  exact g.observe_denote_reindex rows loops m env wf newWF i

end Silmaril.SSA.PEG
