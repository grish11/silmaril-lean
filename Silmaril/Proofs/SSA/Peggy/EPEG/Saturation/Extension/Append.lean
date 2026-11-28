module

public import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Defs
public import Silmaril.SSA.PEG.Rules.Defs
import Silmaril.SSA.PEG.Rules.Thms

public section

namespace Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension

open Silmaril.SSA.PEG
open Silmaril.SSA.Peggy.EPEG.Saturation.Extension
open Silmaril.SSA.RVSDG (Port Tuple)

universe u v x

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}
variable {g : Graph P params results n l} (row : Row g)
variable {m : Interpretation.{u,v,x} P} {env : Tuple m.Value params}

private theorem transport_heq {α : Sort u} {F : α → Sort v} {a b : α} (e : a = b) (value : F a) :
    (e ▸ value : F b) ≍ value := by cases e; rfl

theorem node_old (i : Fin n) : HEq (row.append.node i.castSucc) (row.liftNode (g.node i)) := by
  simp only [Row.append, Fin.lastCases_castSucc]
  exact transport_heq _ _

theorem node_fresh :
    Rules.HasNode (g := row.append) row.fresh row.label (row.args.map fun _ => row.liftRef) := by
  simp only [Rules.HasNode, Row.fresh, Row.append, Fin.lastCases_last]
  exact transport_heq _ _

theorem lift_hasNode {ins : List (Ty Data)} {t : Ty Data}
    {r : Ref g.sort t} {label : Label P params (Fin l) ins t} {args : Tuple (Ref g.sort) ins}
    (shape : Rules.HasNode r label args) :
    Rules.HasNode (g := row.append) (row.liftRef r) label (args.map fun _ => row.liftRef) := by
  have lift_shape {a b : Ty Data} (eq : a = b)
      (lhs : Node P params (Fin l) g.sort a) (rhs : Node P params (Fin l) g.sort b)
      (h : HEq lhs rhs) : HEq (row.liftNode lhs) (row.liftNode rhs) := by
    subst b
    rw [eq_of_heq h]
  exact (node_old row r.id).trans (lift_shape r.typed _ _ shape)

private theorem get_lift {ins : List (Ty Data)} {t : Ty Data}
    (args : Tuple (Ref g.sort) ins) (port : Port ins t) :
    (args.map fun _ => row.liftRef).get port = row.liftRef (args.get port) := by
  induction port with
  | head => cases args; rfl
  | tail port ih => cases args; apply ih

private theorem edge_lift {t t' : Ty Data} {child : Fin (n + 1)}
    {kind : EdgeKind (Fin l)} (node : Node P params (Fin l) g.sort t')
    (newNode : Node P params (Fin l) row.sort t)
    (same : t = t')
    (shape : HEq newNode (row.liftNode node))
    (edge : ∃ slot : Fin newNode.inputs.length,
      newNode.label.kind slot = kind ∧ (newNode.arg slot).id = child) :
    ∃ slot : Fin node.inputs.length,
      node.label.kind slot = kind ∧ (node.arg slot).id.castSucc = child := by
  subst t'
  cases eq_of_heq shape
  obtain ⟨slot, role, address⟩ := edge
  refine ⟨slot, role, ?_⟩
  simpa only [Row.liftNode, Node.arg, Node.ofLabel, get_lift, Row.liftRef] using address

private theorem demand_old {i : Fin n} {idx : Index l} {child : Request (n + 1) l}
    (d : row.append.Demand child (i.castSucc, idx)) :
    ∃ j : Fin n, j.castSucc = child.1 ∧ g.Demand (j, child.2) (i, idx) := by
  obtain ⟨kind, edge, changes⟩ := d
  obtain ⟨slot, role, address⟩ := edge_lift row (g.node i) _ (row.sort_old i) (node_old row i) edge
  exact ⟨((g.node i).arg slot).id, address, kind, ⟨slot, role, rfl⟩, changes⟩

private theorem accessible_old (wf : WellFounded g.Demand) (q : Request n l) :
    Acc row.append.Demand (q.1.castSucc, q.2) := by
  induction q using wf.induction with
  | h q ih =>
    constructor
    intro child d
    obtain ⟨j, address, small⟩ := demand_old row d
    obtain ⟨child, idx⟩ := child
    change j.castSucc = child at address
    subst child
    exact ih (j, idx) small

theorem demand_wf (wf : WellFounded g.Demand) : WellFounded row.append.Demand := by
  constructor
  rintro ⟨i, idx⟩
  refine Fin.lastCases (motive := fun j => Acc row.append.Demand (j, idx)) ?_
    (fun j => accessible_old row wf (j, idx)) i
  constructor
  rintro ⟨child, time⟩ ⟨kind, edge, _⟩
  obtain ⟨slot, _, address⟩ :=
    edge_lift row (Node.ofLabel row.label row.args) _ row.sort_fresh (node_fresh row) edge
  change _ = child at address
  subst child
  exact accessible_old row wf (_, time)

private def restrict (values : row.append.Valuation m) : g.Valuation m :=
  fun q => (row.sort_old q.1) ▸ values (q.1.castSucc, q.2)

private theorem transport_trans {α : Sort u} {F : α → Sort v} {a b c : α}
    (e : a = b) (f : b = c) (value : F a) :
    ((e.trans f) ▸ value : F c) = (f ▸ (e ▸ value : F b) : F c) := by
  cases e; cases f; rfl

private theorem read_lift {t : Ty Data} (values : row.append.Valuation m)
    (r : Ref g.sort t) (idx : Index l) :
    Rules.readRef values (row.liftRef r) idx = Rules.readRef (restrict row values) r idx := by
  unfold Rules.readRef Ref.read Row.liftRef restrict
  exact transport_trans (F := fun t => Option (m.Value t)) (row.sort_old r.id) r.typed
    (values (r.id.castSucc, idx))

private theorem restrict_solves {values : row.append.Valuation m}
    (solves : row.append.Solves m env values) : g.Solves m env (restrict row values) := by
  rintro ⟨i, idx⟩
  have old := Rules.at_label solves (r := row.liftRef (Ref.ofId g.sort i)) (node_old row i) idx
  change restrict row values (i, idx) = _
  rw [← show Rules.readRef (restrict row values) (Ref.ofId g.sort i) idx =
    restrict row values (i, idx) from rfl, ← read_lift row, old]
  change (g.node i).label.interpret m env idx _ = (g.node i).label.interpret m env idx _
  congr 1
  funext slot j valid
  exact (congrArg (fun r : Ref row.sort _ => Rules.readRef values r j)
    (get_lift row _ _)).trans (read_lift row values ((g.node i).arg slot) j)

theorem denote_old (wf : WellFounded g.Demand) (after : WellFounded row.append.Demand)
    (idx : Index l) {t : Ty Data} (ref : Ref g.sort t) :
    Rules.readRef (row.append.denote m env after) (row.liftRef ref) idx =
      Rules.readRef (g.denote m env wf) ref idx := by
  rw [read_lift]
  congr 1
  exact g.solves_unique m env wf (restrict_solves row (row.append.denote_solves m env after))
    (g.denote_solves m env wf)

theorem observe (wf : WellFounded g.Demand) (after : WellFounded row.append.Demand) (idx : Index l) :
    row.append.observe m (row.append.denote m env after) idx = g.observe m (g.denote m env wf) idx := by
  have go {ts : List (Ty Data)} (xs : Tuple (Ref g.sort) ts) :
      ((xs.map fun _ => row.liftRef).map fun _ r =>
        Rules.readRef (row.append.denote m env after) r idx) =
      (xs.map fun _ r => Rules.readRef (g.denote m env wf) r idx) := by
    induction xs with
    | nil => rfl
    | cons r xs ih => exact congrArg₂ Tuple.cons (denote_old row wf after idx r) ih
  exact go g.roots

end Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension
