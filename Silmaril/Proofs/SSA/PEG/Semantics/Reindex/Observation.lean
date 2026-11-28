module

public import Silmaril.Proofs.SSA.PEG.Semantics.Reindex.Demand
public import Silmaril.SSA.PEG.Semantics.Thms

public section

namespace Silmaril.SSA.PEG.Semantics.Reindex.Proofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Tuple)

universe u v w

variable {n n' l l' : Nat}
variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)}
variable {g : Graph P params results n l} {m : Interpretation.{u,v,w} P}

private theorem interpret (env : Tuple m.Value params) (loops : Fin l' ≃ Fin l)
    {ins : List (Ty Data)} {out : Ty Data} (label : Label P params (Fin l) ins out)
    (i : Index l') (read : ∀ (slot : Fin ins.length), Index l → Option (m.Value ins[slot])) :
    (label.map (fun op => op) loops.symm).interpret m env i
        (fun slot j _ => read slot (j.reindex loops.symm)) =
      label.interpret m env (i.reindex loops.symm) (fun slot j _ => read slot j) := by
  cases label with
  | param _ | op _ | phi => rfl
  | theta loop =>
    simp only [Label.map, Label.interpret]
    change (match h : i (loops.symm loop) with
      | 0 => read 0 (i.reindex loops.symm)
      | k + 1 => read 1 ((i.set (loops.symm loop) k).reindex loops.symm)) =
      (match h : i (loops.symm loop) with
      | 0 => read 0 (i.reindex loops.symm)
      | k + 1 => read 1 ((i.reindex loops.symm).set loop k))
    generalize tick : i (loops.symm loop) = count
    cases count with
    | zero => rfl
    | succ k =>
      have shifted : (i.set (loops.symm loop) k).reindex loops.symm =
          (i.reindex loops.symm).set loop k := by
        simpa only [Equiv.symm_symm, Equiv.apply_symm_apply] using index_set i loops.symm (loops.symm loop) k
      exact congrArg (read 1) shifted
  | eval loop =>
    simp [Label.map, Label.interpret, index_set]
  | pass loop =>
    simp [Label.map, Label.interpret, index_set]

private theorem read_cast {s : Fin n → Ty Data} {out : Ty Data} {a b : Fin n}
    (same : a = b) (ty : s b = out) (read : ∀ i, Option (m.Value (s i))) :
    ((congrArg s same).trans ty ▸ read a : Option (m.Value out)) = (ty ▸ read b) := by
  cases same
  rfl

private theorem read_ref {s : Fin n → Ty Data} {out : Ty Data} (r : Ref s out)
    (rows : Fin n' ≃ Fin n) (read : ∀ i, Option (m.Value (s i))) :
    (r.reindex rows).read m.carrier (read (rows (r.reindex rows).id)) = r.read m.carrier (read r.id) :=
  read_cast (rows.apply_symm_apply r.id) r.typed read

theorem equation (env : Tuple m.Value params) (rows : Fin n' ≃ Fin n)
    (loops : Fin l' ≃ Fin l) (values : g.Valuation m) (q : Request n' l') :
    (g.reindex rows loops).equation m env (g.reindexValuation m rows loops values) q =
      g.equation m env values (Request.toOriginal rows loops q) := by
  let node := g.node (rows q.1)
  let mapped := node.relabel (fun op => op) rows loops.symm
  let read (slot : Fin node.inputs.length) (j : Index l) :=
    (node.arg slot).read m.carrier (values ((node.arg slot).id, j))
  calc
    _ = mapped.label.interpret m env q.2 (fun slot j _ => read slot (j.reindex loops.symm)) := by
      apply congrArg (mapped.label.interpret m env q.2)
      funext slot j _
      change (mapped.arg slot).read m.carrier
        (values (rows (mapped.arg slot).id, j.reindex loops.symm)) = _
      rw [show mapped.arg slot = (node.arg slot).reindex rows from
        node.arg_relabel (fun op => op) rows loops.symm slot]
      exact read_ref (node.arg slot) rows (fun key => values (key, j.reindex loops.symm))
    _ = _ := interpret env loops node.label q.2 read

theorem denote (env : Tuple m.Value params) (rows : Fin n' ≃ Fin n) (loops : Fin l' ≃ Fin l)
    (wf : WellFounded g.Demand) (mapped : WellFounded (g.reindex rows loops).Demand) :
    (g.reindex rows loops).denote m env mapped = g.reindexValuation m rows loops (g.denote m env wf) := by
  apply (g.reindex rows loops).solves_unique m env mapped
    ((g.reindex rows loops).denote_solves m env mapped)
  intro q
  exact (g.denote_solves m env wf (Request.toOriginal rows loops q)).trans
    (equation env rows loops _ q).symm

private theorem observe_tuple {s : Fin n → Ty Data} {ts : List (Ty Data)}
    (roots : Tuple (Ref s) ts) (rows : Fin n' ≃ Fin n) (read : ∀ i, Option (m.Value (s i))) :
    (roots.map (fun _ r => r.reindex rows)).map (fun _ r => r.read m.carrier (read (rows r.id))) =
      roots.map (fun _ r => r.read m.carrier (read r.id)) := by
  induction roots with
  | nil => rfl
  | cons r _ ih => exact congrArg₂ Tuple.cons (read_ref r rows read) ih

theorem observe (env : Tuple m.Value params) (rows : Fin n' ≃ Fin n) (loops : Fin l' ≃ Fin l)
    (wf : WellFounded g.Demand) (mapped : WellFounded (g.reindex rows loops).Demand) (i : Index l') :
    (g.reindex rows loops).observe m ((g.reindex rows loops).denote m env mapped) i =
      g.observe m (g.denote m env wf) (i.reindex loops.symm) := by
  rw [denote env rows loops wf mapped]
  exact observe_tuple g.roots rows (fun key => g.denote m env wf (key, i.reindex loops.symm))

end Silmaril.SSA.PEG.Semantics.Reindex.Proofs
