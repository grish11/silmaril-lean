module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Defs
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Liveness.Demand.Feedback

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Proofs

open NestedTheta.Liveness
open Feedback.Proofs (DemandLE selectWires_mono reads_mono close_isLeast includes_close_iff)

universe u v
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {entry results : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))} {loops : Bool}
variable {member : Option (MemberSummaries V S)}

theorem resultDemand_mono {pc : Nat} {low high : DemandPlan} (le : low.live ⊆ high.live) :
    ∀ p, resultDemand pc low p = true → resultDemand pc high p = true :=
  fun _ live => List.contains_iff_mem.2 (le (List.contains_iff_mem.1 live))

theorem applyReads_mono {context params : Ports (Ty V S)} {low high : List Address}
    (le : low ⊆ high) {capturePast : List (Ports (Ty V S))} (captures : Wires entry capturePast context) (arguments : Wires entry past params) :
    applyReads low captures arguments ⊆ applyReads high captures arguments := by
  intro a h
  simp only [applyReads, List.mem_append] at h ⊢
  exact h.imp
    (fun present => selectWires_mono captures
      (fun _ _ h => List.contains_iff_mem.2 (le (List.contains_iff_mem.1 h))) present)
    (fun present => selectWires_mono arguments
      (fun _ _ h => List.contains_iff_mem.2 (le (List.contains_iff_mem.1 h))) present)

theorem prepend_mono {pc : Nat} {less more : List Address} {low high : DemandPlan}
    (next : low.live ⊆ high.live) (reads : less ⊆ more) :
    (low.prepend pc less).live ⊆ (high.prepend pc more).live := by
  intro a h
  simp only [DemandPlan.prepend, transfer, List.mem_append, List.mem_filter] at h ⊢
  exact h.imp (fun h => reads h) (fun ⟨live, kept⟩ => ⟨next live, kept⟩)

theorem plan_mono (code : Code Op entry past sigs results loops member) {low high : Demand}
    (more : ∀ p, low p = true → high p = true) : (code.plan low).live ⊆ (code.plan high).live := by
  induction code generalizing low high with
  | ret wires =>
    apply prepend_mono (fun _ h => h) (selectWires_mono wires ?_)
    intro ty i h
    cases ty with
    | state => rfl
    | control | value => exact more i h
  | primitive _ _ _ ih => exact prepend_mono (ih more) (fun _ h => h)
  | apply _ captures _ arguments _ ihBody ihRest =>
    exact prepend_mono (ihRest more)
      (applyReads_mono (ihBody (resultDemand_mono (ihRest more))) captures arguments)
  | @gamma _ _ captures outs _ _ _ _ extra _ selector wires arms rest ihArm ihRest =>
    let kind : NestedTheta.Kind (Instruction Op) (.control (extra + 2) :: captures) outs := .base (.gamma extra)
    exact prepend_mono (ihRest more)
      (reads_mono kind (.cons selector wires) _ (ihRest more)
        (fun i requested => ((arms i).plan requested).live) (fun i _ _ more => ihArm i more))
  | @theta _ _ carried _ _ _ _ wires body rest ihBody ihRest =>
    exact prepend_mono (ihRest more)
      (reads_mono (.theta (Op := Instruction Op) carried) wires _ (ihRest more)
        (fun _ requested => (body.plan requested).live) (fun _ _ _ more => ihBody more))

  | @callAt _ _ _ _ table i _ captures arguments _ ih =>
    exact prepend_mono (ih more)
      (applyReads_mono (table.monotone i (resultDemand_mono (ih more))) captures arguments)

theorem feedback_isLeast {carried : Ports (Ty V S)}
    (body : Code Op carried [] sigs (Theta.BodyResults carried) true member) (exit : Demand) :
    IsLeast {live | Feedback.step exit (fun demand => (body.plan demand).live) live = live}
      (body.feedbackLive exit) :=
  close_isLeast exit _ (plan_mono body)

theorem includes_feedback_iff {carried : Ports (Ty V S)}
    (body : Code Op carried [] sigs (Theta.BodyResults carried) true member) (exit : Demand)
    {ty : Ty V S} (p : Port carried ty) :
    Feedback.includes (body.feedbackLive exit) p.index = true ↔
      Address.arg p.index ∈ (body.plan (Feedback.bodyDemand exit (body.feedbackLive exit))).live :=
  includes_close_iff p exit _ (plan_mono body)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Proofs
