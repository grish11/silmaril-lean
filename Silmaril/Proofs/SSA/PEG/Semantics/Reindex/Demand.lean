module

public import Silmaril.SSA.PEG.Semantics.Reindex.Defs
public import Silmaril.SSA.PEG.Thms
import Silmaril.Proofs.SSA.PEG.Graph

public section

namespace Silmaril.SSA.PEG.Semantics.Reindex.Proofs

universe u v

variable {n n' l l' : Nat}
variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)}

theorem index_inverse (i : Index l) (loops : Fin l' ≃ Fin l) :
    (i.reindex loops).reindex loops.symm = i := by
  funext j
  simp [Index.reindex]

theorem index_set (i : Index l) (loops : Fin l' ≃ Fin l) (key : Fin l) (k : Nat) :
    (i.set key k).reindex loops = (i.reindex loops).set (loops.symm key) k := by
  funext j
  have same : loops j = key ↔ j = loops.symm key := by
    exact ⟨fun h => by simpa using congrArg loops.symm h,
      fun h => by simpa using congrArg loops h⟩
  simp [Index.reindex, Index.set, same]

theorem changes (loops : Fin l' ≃ Fin l) (kind : EdgeKind (Fin l')) (i j : Index l') :
    kind.Changes i j ↔ (kind.map loops).Changes (i.reindex loops.symm) (j.reindex loops.symm) := by
  have eq (a b : Index l') : a = b ↔ a.reindex loops.symm = b.reindex loops.symm := by
    constructor
    · exact congrArg (fun q : Index l' => q.reindex loops.symm)
    · intro h
      exact (index_inverse a loops.symm).symm.trans
        ((congrArg (fun q : Index l => q.reindex loops) h).trans (index_inverse b loops.symm))
  have atKey (key : Fin l') : (i.reindex loops.symm) (loops key) = i key := by
    simp [Index.reindex]
  have set (key : Fin l') (k : Nat) :
      (i.reindex loops.symm).set (loops key) k = (i.set key k).reindex loops.symm :=
    (index_set i loops.symm key k).symm
  cases kind
  · exact eq j i
  · simp only [EdgeKind.map, EdgeKind.Changes, atKey, ← eq]
  · simp only [EdgeKind.map, EdgeKind.Changes, atKey, set, ← eq]
  · simp only [EdgeKind.map, EdgeKind.Changes, set, ← eq]
  · exact eq j i

theorem demand (g : Graph P params results n l) (rows : Fin n' ≃ Fin n)
    (loops : Fin l' ≃ Fin l) (p q : Request n' l') :
    (g.reindex rows loops).Demand p q ↔
      g.Demand (Request.toOriginal rows loops p) (Request.toOriginal rows loops q) := by
  constructor
  · rintro ⟨kind, edge, moved⟩
    exact ⟨kind.map loops, (g.edge_relabel (fun op => op) rows loops _ _ kind).mp edge,
      (changes loops kind q.2 p.2).mp moved⟩
  · rintro ⟨kind, edge, moved⟩
    let localKind := kind.map loops.symm
    have same : localKind.map loops = kind := Silmaril.SSA.PEG.Proofs.mapKind_symm_inv loops kind
    refine ⟨localKind, (g.edge_relabel (fun op => op) rows loops _ _ localKind).mpr ?_,
      (changes loops localKind q.2 p.2).mpr ?_⟩
    · rw [same]
      exact edge
    · rw [same]
      exact moved

theorem demand_wf (g : Graph P params results n l) (rows : Fin n' ≃ Fin n) (loops : Fin l' ≃ Fin l) :
    WellFounded (g.reindex rows loops).Demand ↔ WellFounded g.Demand := by
  constructor
  · intro wf
    refine Subrelation.wf (r := InvImage (g.reindex rows loops).Demand
      (Request.toOriginal rows.symm loops.symm)) (fun {a b} h => ?_) (InvImage.wf _ wf)
    apply (demand g rows loops _ _).mpr
    simpa [Request.toOriginal, index_inverse] using h
  · intro wf
    exact Subrelation.wf (r := InvImage g.Demand (Request.toOriginal rows loops))
      (fun {a b} step => (demand g rows loops a b).mp step) (InvImage.wf _ wf)

end Silmaril.SSA.PEG.Semantics.Reindex.Proofs
