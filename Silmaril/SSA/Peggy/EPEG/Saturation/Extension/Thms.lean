module

public import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.ZeroSample
public import Silmaril.SSA.Peggy.EPEG.Saturation.Thms
import Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Append
import Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Replay
import Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.ZeroSample

public section

namespace Silmaril.SSA.Peggy.EPEG.Saturation.Extension

open PEG
open RVSDG (Tuple)

universe u v x

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}
variable {g : Graph P params results n l} {s : State P params results n l}
variable {m : Interpretation.{u,v,x} P} {env : Tuple m.Value params}

theorem Row.node_old (row : Row g) (i : Fin n) :
    HEq (row.append.node i.castSucc) (row.liftNode (g.node i)) :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.node_old row i

theorem Row.node_fresh (row : Row g) :
    Rules.HasNode (g := row.append) row.fresh row.label (row.args.map fun _ => row.liftRef) :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.node_fresh row

theorem Row.lift_hasNode (row : Row g) {inputs : List (Ty Data)} {out : Ty Data}
    {ref : Ref g.sort out} {label : Label P params (Fin l) inputs out} {args : Tuple (Ref g.sort) inputs}
    (shape : Rules.HasNode ref label args) :
    Rules.HasNode (g := row.append) (row.liftRef ref) label (args.map fun _ => row.liftRef) :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.lift_hasNode row shape

/-- Old demands are unchanged under the injection, and every demand of
the new row goes to the old table, even for an unbounded sampling edge. -/
theorem Row.demandWellFounded (row : Row g) (wf : WellFounded g.Demand) :
    WellFounded row.append.Demand :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.demand_wf row wf

theorem Row.read_old (row : Row g) (wf : WellFounded g.Demand) (after : WellFounded row.append.Demand)
    {t : Ty Data} (ref : Ref g.sort t) (idx : Index l) :
    Rules.readRef (row.append.denote m env after) (row.liftRef ref) idx =
      Rules.readRef (g.denote m env wf) ref idx :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.denote_old row wf after idx ref

theorem Row.observe_eq (row : Row g) (wf : WellFounded g.Demand)
    (after : WellFounded row.append.Demand) (idx : Index l) :
    row.append.observe m (row.append.denote m env after) idx =
      g.observe m (g.denote m env wf) idx :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.observe row wf after idx

/-- Together with the retained rows and ordered roots, this gives the
append-only instance of (4.1). Class names can change. -/
theorem Step.extends (step : Step s) {a b : Fin n} (joined : s.classes a = s.classes b) :
    step.apply.classes a.castSucc = step.apply.classes b.castSucc :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.step_extends step joined

theorem Step.sound (step : Step s) (wf : WellFounded s.graph.Demand)
    (valid : s.classes.Valid (s.graph.denote m env wf)) (holds : step.Holds env) :
    step.apply.classes.Valid (step.apply.graph.denote m env (step.row.demandWellFounded wf)) :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.step_sound step wf valid holds
    (step.row.demandWellFounded wf)

theorem Plan.demandWellFounded (fuel : Nat) (plan : Plan s) (wf : WellFounded s.graph.Demand) :
    WellFounded (plan.run fuel).2.graph.Demand :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.plan_wf fuel plan wf

theorem Plan.address (fuel : Nat) (plan : Plan s) {t : Ty Data} (ref : Ref s.graph.sort t) :
    (plan.liftRef fuel ref).id.val = ref.id.val :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.plan_address fuel plan ref

theorem Plan.extends (fuel : Nat) (plan : Plan s) {t t' : Ty Data}
    (a : Ref s.graph.sort t) (b : Ref s.graph.sort t') (joined : s.classes a.id = s.classes b.id) :
    (plan.run fuel).2.classes (plan.liftRef fuel a).id =
      (plan.run fuel).2.classes (plan.liftRef fuel b).id :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.plan_extends fuel plan a b joined

theorem Plan.read_old (fuel : Nat) (plan : Plan s) (wf : WellFounded s.graph.Demand)
    {t : Ty Data} (ref : Ref s.graph.sort t) (idx : Index l) :
    Rules.readRef ((plan.run fuel).2.graph.denote m env (plan.demandWellFounded fuel wf))
      (plan.liftRef fuel ref) idx = Rules.readRef (s.graph.denote m env wf) ref idx :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.plan_read fuel plan wf ref idx

theorem Plan.observe_eq (fuel : Nat) (plan : Plan s) (wf : WellFounded s.graph.Demand) (idx : Index l) :
    let target := (plan.run fuel).2.graph
    target.observe m (target.denote m env (plan.demandWellFounded fuel wf)) idx =
      s.graph.observe m (s.graph.denote m env wf) idx :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.plan_observe fuel plan wf idx

/-- At any budget, the replay preserves ordered partial observations and
establishes semantic equality for all final class pairs. -/
theorem Plan.sound (fuel : Nat) (plan : Plan s) (wf : WellFounded s.graph.Demand)
    (valid : s.classes.Valid (s.graph.denote m env wf)) (holds : plan.Holds env fuel) :
    let target := (plan.run fuel).2
    let after := plan.demandWellFounded fuel wf
    target.classes.Valid (target.graph.denote m env after) ∧
      ∀ idx, target.graph.observe m (target.graph.denote m env after) idx =
        s.graph.observe m (s.graph.denote m env wf) idx :=
  ⟨Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.plan_valid fuel plan wf valid holds,
    plan.observe_eq fuel wf⟩

theorem ZeroSample.holds {site : Fin n} {zero : P [] .count}
    (found : ZeroSample s.graph site zero) (law : m.run zero .nil = some ⟨0⟩) :
    found.step.Holds env :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.zeroSample_step_holds found law

theorem ZeroSample.equates {site : Fin n} {zero : P [] .count}
    (found : ZeroSample s.graph site zero) :
    found.step.apply.classes site.castSucc = found.step.apply.classes (Fin.last n) :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.zeroSample_equates found

end Silmaril.SSA.Peggy.EPEG.Saturation.Extension
