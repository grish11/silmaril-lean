module

public import Silmaril.Proofs.SSA.PEG.Semantics.Reindex.Demand
import Silmaril.Proofs.SSA.PEG.Graph

public section

namespace Silmaril.SSA.PEG.Semantics.Reindex.Proofs

universe u v

variable {n n' l l' : Nat}
variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)}

private theorem component_change (c : RankComponent n l) (rows : Fin n' ≃ Fin n)
    (loops : Fin l' ≃ Fin l) (a b : Fin n') (kind : EdgeKind (Fin l')) :
    (c.reindex rows loops).change a b kind = c.change (rows a) (rows b) (kind.map loops) := by
  cases c with
  | phase _ => rfl
  | counter key =>
    have same (j : Fin l') : loops.symm key = j ↔ key = loops j := by
      rw [← loops.apply_eq_iff_eq, loops.apply_symm_apply]
    cases kind <;> simp [RankComponent.reindex, RankComponent.change, EdgeKind.map, same]

private theorem check_edge (rank : DemandRank n l) (rows : Fin n' ≃ Fin n)
    (loops : Fin l' ≃ Fin l) (a b : Fin n') (kind : EdgeKind (Fin l')) :
    (rank.reindex rows loops).checkEdge a b kind =
      rank.checkEdge (rows a) (rows b) (kind.map loops) := by
  induction rank with
  | nil => rfl
  | cons c cs ih =>
    simp only [DemandRank.reindex, List.map_cons, DemandRank.checkEdge, component_change]
    split <;> simp_all only [DemandRank.reindex]

private theorem check_iff_edges (g : Graph P params results n l) (rank : DemandRank n l) :
    rank.check g = true ↔ ∀ a b kind, g.Edge a kind b → rank.checkEdge a b kind = true := by
  constructor
  · intro ok a b kind edge
    obtain ⟨slot, label, arg⟩ := edge
    have row := List.all_eq_true.mp (List.all_eq_true.mp ok a (List.mem_finRange a))
      slot (List.mem_finRange slot)
    simpa only [label, arg] using row
  · intro ok
    apply List.all_eq_true.mpr
    intro a _
    apply List.all_eq_true.mpr
    intro slot _
    exact ok _ _ _ ⟨slot, rfl, rfl⟩

theorem rank_check (g : Graph P params results n l) (rank : DemandRank n l)
    (rows : Fin n' ≃ Fin n) (loops : Fin l' ≃ Fin l) :
    (rank.reindex rows loops).check (g.reindex rows loops) = rank.check g := by
  apply Bool.eq_iff_iff.mpr
  simp only [check_iff_edges, check_edge]
  constructor
  · intro ok a b kind edge
    let localKind := kind.map loops.symm
    have same : localKind.map loops = kind := Silmaril.SSA.PEG.Proofs.mapKind_symm_inv loops kind
    have localEdge : (g.reindex rows loops).Edge (rows.symm a) localKind (rows.symm b) :=
      (g.edge_relabel (fun op => op) rows loops _ _ localKind).mpr (by simpa [same] using edge)
    simpa [same] using ok _ _ _ localEdge
  · intro ok a b kind edge
    exact ok _ _ _ ((g.edge_relabel (fun op => op) rows loops _ _ kind).mp edge)

end Silmaril.SSA.PEG.Semantics.Reindex.Proofs
