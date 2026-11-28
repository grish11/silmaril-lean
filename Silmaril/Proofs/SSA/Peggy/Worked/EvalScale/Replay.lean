module

public import Silmaril.SSA.Peggy.Worked.EvalScale.Defs
public import Silmaril.SSA.Peggy.EPEG.Selection.Thms
import Silmaril.Proofs.SSA.Peggy.Worked.EvalScale.Rule
import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Comparison.Thms
import Silmaril.SSA.PEG.Rules.Thms

public section

namespace Silmaril.Proofs.SSA.Peggy.Worked.EvalScale

open Silmaril.SSA.PEG
open Silmaril.SSA.Peggy.EPEG
open Silmaril.SSA.Peggy.EPEG.Saturation.Extension
open Silmaril.SSA.Peggy.Worked.EvalScale
open Silmaril.SSA.RVSDG (Port Tuple)

universe u v x

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}
variable {s : State P params results n l} {site : Fin n} {factor : P [] .count}
variable {m : Interpretation.{u,v,x} P} {env : Tuple m.Value params}
variable {op : P [.count, .count] .count}

private theorem lift_shape (step : Step s) {out : Ty Data} {inputs : List (Ty Data)}
    {r : Ref s.graph.sort out} {label : Label P params (Fin l) inputs out}
    {args : Tuple (Ref s.graph.sort) inputs} (shape : Rules.HasNode r label args) :
    Rules.HasNode (g := step.apply.graph) (step.row.liftRef r) label
      (args.map fun _ => step.row.liftRef) := by
  have lifted := step.embedding.hasNode shape
  change Rules.HasNode (g := step.apply.graph) (step.embedding.vertices.ref r) label
    (step.embedding.vertices.tuple args) at lifted
  rw [step.embedding_vertices] at lifted
  exact lifted

theorem equation_holds (found : Match s.graph site factor op)
    (law : Law m factor op) {values : found.outside.append.Valuation m}
    (solves : found.outside.append.Solves m env values) : found.equation.Holds values := by
  intro _
  obtain ⟨k, literal, total⟩ := law
  let first := found.appendInside
  let second := found.appendOutside
  have outer := lift_shape second (lift_shape first found.outer)
  have sample := lift_shape second (lift_shape first found.sample)
  have product := lift_shape second found.inside.node_fresh
  have target := found.outside.node_fresh
  have fixed := lift_shape second (lift_shape first found.literal)
  have constant (i : Index l) :
      Rules.readRef values (found.outside.liftRef (found.inside.liftRef found.constant)) i = some k :=
    (Rules.at_label solves fixed i).trans literal
  exact (Rules.streamEq_iff_vertex (g := found.outside.append) (values := values)
    found.oldResult found.outside.fresh).mp
    (commute solves outer sample product target k constant total)

theorem plan_holds (found : Match s.graph site factor op) (law : Law m factor op) :
    found.plan.Holds env 2 := by
  refine ⟨?_, ?_, trivial⟩
  · intro _ _ _ member
    cases member
  · intro values solves reason member
    have same : reason = .guarded found.equation := List.mem_singleton.mp member
    subst reason
    exact equation_holds found law solves

theorem equates (found : Match s.graph site factor op) :
    found.saturated.classes found.oldResult.id = found.saturated.classes found.outside.fresh.id := by
  let reason : Saturation.Obligation found.outside.append := .guarded found.equation
  exact Saturation.saturate_closed [reason] (Row.liftClasses found.appendInside.apply.classes)
    reason (by simp) rfl

private theorem get_redirect (found : Match s.graph site factor op) {ts : List (Ty Data)}
    {out : Ty Data} (xs : Tuple (Ref found.outside.sort) ts) (port : Port ts out) :
    ((xs.map fun _ => found.redirect).get port) = found.redirect (xs.get port) := by
  induction port with
  | head => cases xs; rfl
  | tail port ih => cases xs; apply ih

theorem check_of_rank (found : Match s.graph site factor op) (rank : DemandRank (n + 2) l)
    (ranked : rank.check found.extract = true) : found.checkExtraction rank = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply Bool.and_eq_true_iff.mpr ⟨ranked, List.all_eq_true.mpr ?_⟩
    intro i _
    let port := portAt results i
    let roots : Tuple (Ref found.outside.sort) results := found.outside.append.roots
    let classes := found.saturated.classes
    change (classes (roots.get port).id == classes ((roots.map fun _ => found.redirect).get port).id) = true
    rw [get_redirect found roots port]
    apply beq_iff_eq.mpr
    unfold Match.redirect
    split
    · rename_i same
      change classes (roots.get port).id = classes found.outside.fresh.id
      rw [same]
      exact equates found
    · rfl
  · apply List.all_eq_true.mpr
    intro i _
    apply List.all_eq_true.mpr
    intro slot _
    exact beq_self_eq_true _

theorem extract_sound (found : Match s.graph site factor op) (wf : WellFounded s.graph.Demand)
    (valid : s.classes.Valid (s.graph.denote m env wf)) (law : Law m factor op)
    (rank : DemandRank (n + 2) l) (checked : found.checkExtraction rank = true) (i : Index l) :
    s.graph.observe m (s.graph.denote m env wf) i =
      found.extract.observe m (found.extract.denote m env
        ((found.selection rank).demandWellFounded (Bool.and_eq_true_iff.mp checked).1)) i := by
  have replay := found.plan.sound 2 wf valid (plan_holds found law)
  have select := Selection.observe_sound_of_rows (found.plan.demandWellFounded 2 wf) replay.1
    (Bool.and_eq_true_iff.mp checked).1 (found.rows rank) (Bool.and_eq_true_iff.mp checked).2 i
  exact (replay.2 i).symm.trans select

end Silmaril.Proofs.SSA.Peggy.Worked.EvalScale
