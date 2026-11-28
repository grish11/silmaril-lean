module

public import Silmaril.SSA.PEG.SortMap.Defs
public import Silmaril.SSA.PEG.Semantics.Thms

public section

namespace Silmaril.SSA.PEG.SortMapProofs

open RVSDG (Port Tuple)

universe u u' v v' w

variable {D : Type u} {E : Type u'} {f : D → E}
variable {P : InstructionSet.{u,v} D} {Q : InstructionSet.{u',v'} E}
variable {params ins results : List (Ty D)} {out : Ty D} {n l : Nat} {L : Type}
variable {sort : Fin n → Ty D}

private def mapSlot (f : D → E) (ts : List (Ty D)) :
    Fin ts.length ≃ Fin (Ty.mapProfile f ts).length :=
  { toFun := fun i => ⟨i.val, by simpa only [Ty.mapProfile, List.length_map] using i.isLt⟩
    invFun := fun i => ⟨i.val, by simpa only [Ty.mapProfile, List.length_map] using i.isLt⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem get_mapDataTuple {A : Ty D → Type v} {B : Ty E → Type v'}
    (each : ∀ t, A t → B (t.mapData f)) (args : Tuple A ins) (p : Port ins out) :
    (mapDataTuple f each args).get (mapDataPort f p) = each _ (args.get p) := by
  induction p with
  | head => cases args; rfl
  | tail p ih => cases args with | cons x xs => exact ih xs

private theorem kind (op : ProfileMap f P Q) (label : Label P params L ins out) (slot : Fin ins.length) :
    (label.mapData op).kind (mapSlot f ins slot) = label.kind slot := by
  cases label <;> rfl

private theorem loop (op : ProfileMap f P Q) (label : Label P params L ins out) :
    (label.mapData op).loop = label.loop := by cases label <;> rfl

private theorem thetaLoop (op : ProfileMap f P Q) (label : Label P params L ins out) :
    (label.mapData op).thetaLoop = label.thetaLoop := by cases label <;> rfl

private theorem tuple_arg_id (args : Tuple (Ref sort) ins) (slot : Fin ins.length) :
    ((mapDataTuple f (fun _ => Ref.mapData f) args).get
      (portAt (Ty.mapProfile f ins) (mapSlot f ins slot))).id =
        (args.get (portAt ins slot)).id := by
  induction args with
  | nil => exact slot.elim0
  | cons ref rest ih =>
    refine Fin.cases ?_ (fun j => ?_) slot
    · rfl
    · exact ih j

private theorem arg_id (op : ProfileMap f P Q) (row : Node P params L sort out)
    (slot : Fin row.inputs.length) :
    ((row.mapData op).arg (mapSlot f row.inputs slot)).id = (row.arg slot).id :=
  tuple_arg_id row.args slot

variable (op : ProfileMap f P Q) (g : Graph P params results n l)

theorem edge (a b : Fin n) (k : EdgeKind (Fin l)) :
    (g.mapData op).Edge a k b ↔ g.Edge a k b := by
  have transport (slot : Fin (g.node a).inputs.length) :
      (g.node a |>.mapData op).label.kind (mapSlot f _ slot) = k ∧
        ((g.node a |>.mapData op).arg (mapSlot f _ slot)).id = b ↔
      (g.node a).label.kind slot = k ∧ ((g.node a).arg slot).id = b := by
    have role := kind op (g.node a).label slot
    exact and_congr (congrArg (· = k) role).to_iff
      (congrArg (· = b) (arg_id op (g.node a) slot)).to_iff
  constructor
  · rintro ⟨slot, h⟩
    obtain ⟨oldSlot, rfl⟩ := (mapSlot f (g.node a).inputs).surjective slot
    exact ⟨oldSlot, (transport oldSlot).mp h⟩
  · rintro ⟨slot, h⟩
    exact ⟨mapSlot f _ slot, (transport slot).mpr h⟩

theorem demand (p q : Request n l) : (g.mapData op).Demand p q ↔ g.Demand p q := by
  simp only [Graph.Demand, edge op g]

theorem demandWellFounded : WellFounded (g.mapData op).Demand ↔ WellFounded g.Demand :=
  ⟨Subrelation.wf fun h => (demand op g _ _).mpr h,
    Subrelation.wf fun h => (demand op g _ _).mp h⟩

theorem wellFormed : (g.mapData op).WellFormed ↔ g.WellFormed := by
  have rel : (g.mapData op).Edge = g.Edge :=
    funext fun a => funext fun k => funext fun b => propext (edge op g a b k)
  have feedback : (g.mapData op).FeedbackCycles = g.FeedbackCycles := by
    unfold Graph.FeedbackCycles
    rw [rel]
  have scopeEq : (g.mapData op).Scoped = g.Scoped := by
    unfold Graph.Scoped
    rw [rel]
    simp only [Graph.mapData, Node.mapData, loop, thetaLoop]
  have outer : (g.mapData op).OuterFeedbackCycles = g.OuterFeedbackCycles := by
    unfold Graph.OuterFeedbackCycles
    rw [rel]
    rfl
  exact ⟨fun h => ⟨h.forest, feedback ▸ h.feedback, scopeEq ▸ h.loopScope, outer ▸ h.outerFeedback⟩,
    fun h => ⟨h.forest, feedback.symm ▸ h.feedback, scopeEq.symm ▸ h.loopScope, outer.symm ▸ h.outerFeedback⟩⟩

end Silmaril.SSA.PEG.SortMapProofs
