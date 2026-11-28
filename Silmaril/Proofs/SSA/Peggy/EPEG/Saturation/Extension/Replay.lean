module

public import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Defs
public import Silmaril.SSA.PEG.Rules.Defs
import Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Append
import Silmaril.SSA.PEG.Rules.Thms
import Silmaril.SSA.Peggy.EPEG.Saturation.Thms

public section

namespace Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension

open Silmaril.SSA.PEG
open Silmaril.SSA.Peggy.EPEG
open Silmaril.SSA.Peggy.EPEG.Saturation.Extension
open Silmaril.SSA.RVSDG (Tuple)

universe u v x

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}
variable {s : State P params results n l} {m : Interpretation.{u,v,x} P}
variable {env : Tuple m.Value params}

private theorem lift_valid (row : Row s.graph) (wf : WellFounded s.graph.Demand)
    (valid : s.classes.Valid (s.graph.denote m env wf))
    (after : WellFounded row.append.Demand) :
    (Row.liftClasses s.classes).Valid (row.append.denote m env after) := by
  intro a b
  induction a using Fin.lastCases <;> induction b using Fin.lastCases
  · exact fun _ => ⟨rfl, fun _ => HEq.rfl⟩
  · rename_i b
    intro joined
    have impossible : n = (s.classes b).val := congrArg Fin.val
      (show Fin.last n = (s.classes b).castSucc by simpa only [Row.liftClasses,
        Fin.lastCases_last, Fin.lastCases_castSucc] using joined)
    exact (Nat.ne_of_lt (s.classes b).isLt impossible.symm).elim
  · rename_i a
    intro joined
    have impossible : (s.classes a).val = n := congrArg Fin.val
      (show (s.classes a).castSucc = Fin.last n by simpa only [Row.liftClasses,
        Fin.lastCases_last, Fin.lastCases_castSucc] using joined)
    exact (Nat.ne_of_lt (s.classes a).isLt impossible).elim
  · rename_i a b
    intro joined
    have eq := valid a b (Fin.castSucc_inj.mp (by simpa only [Row.liftClasses,
      Fin.lastCases_castSucc] using joined))
    let lhs := Ref.ofId s.graph.sort a
    let rhs : Ref s.graph.sort (s.graph.sort a) := ⟨b, eq.1.symm⟩
    have streams := (Rules.streamEq_iff_vertex lhs rhs).mpr eq
    apply (Rules.streamEq_iff_vertex (g := row.append) (values := row.append.denote m env after)
      (row.liftRef lhs) (row.liftRef rhs)).mp
    intro i
    exact (denote_old row wf after i lhs).trans ((streams i).trans (denote_old row wf after i rhs).symm)

theorem step_extends (step : Step s) {a b : Fin n} (joined : s.classes a = s.classes b) :
    step.apply.classes a.castSucc = step.apply.classes b.castSucc := by
  apply Saturation.run_extends step.fuel step.obligations (Row.liftClasses s.classes)
  simp [Row.liftClasses, joined]

theorem step_sound (step : Step s) (wf : WellFounded s.graph.Demand)
    (valid : s.classes.Valid (s.graph.denote m env wf)) (holds : step.Holds env)
    (after : WellFounded step.apply.graph.Demand) :
    step.apply.classes.Valid (step.apply.graph.denote m env after) := by
  apply Saturation.run_denote_sound step.fuel step.obligations after (lift_valid step.row wf valid after)
  exact holds _ (step.row.append.denote_solves m env after)

theorem plan_wf (fuel : Nat) (plan : Plan s) (wf : WellFounded s.graph.Demand) :
    WellFounded (plan.run fuel).2.graph.Demand := by
  induction fuel generalizing n with
  | zero => exact wf
  | succ fuel ih =>
    cases plan with
    | stop => exact wf
    | next step rest => exact ih rest (demand_wf step.row wf)

theorem plan_valid (fuel : Nat) (plan : Plan s) (wf : WellFounded s.graph.Demand)
    (valid : s.classes.Valid (s.graph.denote m env wf)) (holds : plan.Holds env fuel) :
    let target := (plan.run fuel).2
    let after := plan_wf fuel plan wf
    target.classes.Valid (target.graph.denote m env after) := by
  induction fuel generalizing n with
  | zero => exact valid
  | succ fuel ih =>
    cases plan with
    | stop => exact valid
    | next step rest =>
      have after := demand_wf step.row wf
      exact ih rest after (step_sound step wf valid holds.1 after) holds.2

theorem plan_observe (fuel : Nat) (plan : Plan s) (wf : WellFounded s.graph.Demand) (idx : Index l) :
    let target := (plan.run fuel).2.graph
    target.observe m (target.denote m env (plan_wf fuel plan wf)) idx =
      s.graph.observe m (s.graph.denote m env wf) idx := by
  induction fuel generalizing n with
  | zero => rfl
  | succ fuel ih =>
    cases plan with
    | stop => rfl
    | next step rest =>
      have after := demand_wf step.row wf
      exact (ih rest after).trans (observe step.row wf after idx)

theorem plan_read (fuel : Nat) (plan : Plan s) (wf : WellFounded s.graph.Demand)
    {t : Ty Data} (ref : Ref s.graph.sort t) (idx : Index l) :
    Rules.readRef ((plan.run fuel).2.graph.denote m env (plan_wf fuel plan wf))
      (plan.liftRef fuel ref) idx = Rules.readRef (s.graph.denote m env wf) ref idx := by
  induction fuel generalizing n with
  | zero => rfl
  | succ fuel ih =>
    cases plan with
    | stop => rfl
    | next step rest =>
      have after := demand_wf step.row wf
      exact (ih rest after (step.row.liftRef ref)).trans (denote_old step.row wf after idx ref)

theorem plan_address (fuel : Nat) (plan : Plan s) {t : Ty Data} (ref : Ref s.graph.sort t) :
    (plan.liftRef fuel ref).id.val = ref.id.val := by
  induction fuel generalizing n with
  | zero => rfl
  | succ fuel ih =>
    cases plan with
    | stop => rfl
    | next step rest => exact ih rest (step.row.liftRef ref)

theorem plan_extends (fuel : Nat) (plan : Plan s) {t t' : Ty Data}
    (a : Ref s.graph.sort t) (b : Ref s.graph.sort t') (joined : s.classes a.id = s.classes b.id) :
    (plan.run fuel).2.classes (plan.liftRef fuel a).id =
      (plan.run fuel).2.classes (plan.liftRef fuel b).id := by
  induction fuel generalizing n with
  | zero => exact joined
  | succ fuel ih =>
    cases plan with
    | stop => exact joined
    | next step rest => exact ih rest (step.row.liftRef a) (step.row.liftRef b) (step_extends step joined)

end Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension
