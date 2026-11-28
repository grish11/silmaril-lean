module

public import Silmaril.SSA.PEG.Projection.Defs
public import Silmaril.SSA.PEG.Semantics.Thms

public section

namespace Silmaril.SSA.PEG.Projection.Proofs

open RVSDG (Port Tuple)

universe u v w x y

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}
variable {g : Graph P params results n l} (p : g.Projection)

theorem embedding : Function.Injective p.rows.embed := by
  intro a b same
  exact Fin.ext (p.unique.eq_of_getElem_eq a.isLt b.isLt same)

private theorem get_map {F : Ty Data → Type x} {G : Ty Data → Type y} {ts : List (Ty Data)} {t : Ty Data}
    (xs : Tuple F ts) (f : ∀ t, F t → G t) (port : Port ts t) :
    (xs.map f).get port = f _ (xs.get port) := by
  induction port with
  | head => cases xs; rfl
  | tail _ ih => cases xs with | cons _ tail => exact ih tail

theorem operand (i : Fin p.rows.length) (slot : Fin (p.graph.node i).inputs.length) :
    pushRef p.rows ((p.graph.node i).arg slot) = (g.node (p.rows.embed i)).arg slot := by
  let port := portAt (g.node (p.rows.embed i)).inputs slot
  exact (get_map (p.args i).refs (fun _ => pushRef p.rows) port).symm.trans
    (congrArg (fun refs => refs.get port) (p.args i).agrees)

theorem edge (a b : Fin p.rows.length) (kind : EdgeKind (Fin l)) :
    p.graph.Edge a kind b ↔ g.Edge (p.rows.embed a) kind (p.rows.embed b) := by
  have wire (slot : Fin (p.graph.node a).inputs.length) :=
    congrArg Ref.id (operand p a slot)
  constructor
  · rintro ⟨slot, label, arg⟩
    exact ⟨slot, label, (wire slot).symm.trans (congrArg p.rows.embed arg)⟩
  · rintro ⟨slot, label, arg⟩
    exact ⟨slot, label, embedding p ((wire slot).trans arg)⟩

theorem walk {a b : Fin p.rows.length} {ks : List (EdgeKind (Fin l))}
    (path : Walk p.graph.Edge a ks b) : Walk g.Edge (p.rows.embed a) ks (p.rows.embed b) := by
  induction path with
  | nil => exact .nil _
  | cons step _ ih => exact .cons ((edge p _ _ _).mp step) ih

theorem scoped_of (h : g.Scoped) : p.graph.Scoped := by
  intro a b ks start target path first last
  exact h _ _ ks start target (walk p path) first last

theorem demand (q r : Request p.rows.length l) :
    p.graph.Demand q r ↔ g.Demand (p.request q) (p.request r) := by
  constructor
  · rintro ⟨kind, step, changes⟩
    exact ⟨kind, (edge p _ _ _).mp step, changes⟩
  · rintro ⟨kind, step, changes⟩
    exact ⟨kind, (edge p _ _ _).mpr step, changes⟩

theorem predecessor {q : Request p.rows.length l} {r : Request n l}
    (h : g.Demand r (p.request q)) : ∃ s, p.request s = r ∧ p.graph.Demand s q := by
  obtain ⟨kind, ⟨slot, label, target⟩, changes⟩ := h
  let s : Request p.rows.length l := (((p.graph.node q.1).arg slot).id, r.2)
  have wire : (p.request s).1 = r.1 := (congrArg Ref.id (operand p q.1 slot)).trans target
  exact ⟨s, Prod.ext wire rfl, kind, ⟨slot, label, rfl⟩, changes⟩

theorem demandWf (wf : WellFounded g.Demand) : WellFounded p.graph.Demand :=
  Subrelation.wf (r := InvImage g.Demand p.request)
    (fun {q r} step => (demand p q r).mp step) (InvImage.wf _ wf)

private theorem rankEdge (rank : DemandRank n l)
    (a b : Fin p.rows.length) (kind : EdgeKind (Fin l)) :
    (p.rank rank).checkEdge a b kind = rank.checkEdge (p.rows.embed a) (p.rows.embed b) kind := by
  induction rank with
  | nil => rfl
  | cons c cs ih =>
    have same :
        (c.project p.rows).change a b kind =
        c.change (p.rows.embed a) (p.rows.embed b) kind := by
      cases c <;> rfl
    simp only [Graph.Projection.rank, List.map_cons, DemandRank.checkEdge, same]
    split <;> simp_all only [Graph.Projection.rank]

theorem rankCheck (rank : DemandRank n l) (h : rank.check g = true) :
    (p.rank rank).check p.graph = true := by
  apply List.all_eq_true.mpr
  intro a _
  apply List.all_eq_true.mpr
  intro slot _
  have checked := List.all_eq_true.mp
    (List.all_eq_true.mp h (p.rows.embed a) (List.mem_finRange _)) slot (List.mem_finRange _)
  have wire : p.rows.embed ((p.graph.node a).arg slot).id = ((g.node (p.rows.embed a)).arg slot).id :=
    congrArg Ref.id (operand p a slot)
  rw [rankEdge, wire]
  exact checked

variable (m : Interpretation.{u,v,w} P) (env : Tuple m.Value params)

theorem equation (values : g.Valuation m) (q : Request p.rows.length l) :
    p.graph.equation m env (p.valuation m values) q = g.equation m env values (p.request q) := by
  let node := p.graph.node q.1
  let original := g.node (p.rows.embed q.1)
  change node.label.interpret m env q.2
      (fun slot j _ => (node.arg slot).read m.carrier (values (p.rows.embed (node.arg slot).id, j))) =
    original.label.interpret m env q.2
      (fun slot j _ => (original.arg slot).read m.carrier (values ((original.arg slot).id, j)))
  apply congrArg (original.label.interpret m env q.2)
  funext slot j _
  exact congrArg (fun r => r.read m.carrier (values (r.id, j))) (operand p q.1 slot)

theorem solves {values : g.Valuation m} (h : g.Solves m env values) :
    p.graph.Solves m env (p.valuation m values) :=
  fun q => (h (p.request q)).trans (equation p m env values q).symm

theorem denote (wf : WellFounded g.Demand) (localWf : WellFounded p.graph.Demand) :
    p.graph.denote m env localWf = p.valuation m (g.denote m env wf) :=
  p.graph.solves_unique m env localWf (p.graph.denote_solves m env localWf)
    (solves p m env (g.denote_solves m env wf))

private theorem observe_wires {ts : List (Ty Data)}
    (refs : Tuple (Ref (g.sort ∘ p.rows.embed)) ts) (values : g.Valuation m) (i : Index l) :
    refs.map (fun _ r => r.read m.carrier (values (p.rows.embed r.id, i))) =
      (refs.map (fun _ => pushRef p.rows)).map (fun _ r => r.read m.carrier (values (r.id, i))) := by
  induction refs with
  | nil => rfl
  | cons _ _ ih => exact congrArg₂ Tuple.cons rfl ih

theorem observe (wf : WellFounded g.Demand) (localWf : WellFounded p.graph.Demand) (i : Index l) :
    p.graph.observe m (p.graph.denote m env localWf) i = g.observe m (g.denote m env wf) i := by
  rw [denote p m env wf localWf]
  change _ = g.roots.map _
  rw [← p.roots.agrees]
  exact observe_wires p m p.roots.refs _ i

end Silmaril.SSA.PEG.Projection.Proofs
