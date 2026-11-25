module

public import Silmaril.SSA.RVSDG.Theta.Petri.Defs
public import Silmaril.SSA.RVSDG.Petri.Thms

public section

namespace Silmaril.SSA.RVSDG.Theta.Petri.Proofs

universe u v w

open Relation (ReflTransGen)

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {carried : Ports (PortType V S)} {sigs : List (Ports (PortType V S))}

private theorem prepend_repeats {X : Type w} {body : X → Bool → X → Prop}
    {start current : X} (before : ReflTransGen (fun i o => body i true o) start current)
    {output : X} (after : Iterate body current output) : Iterate body start output := by
  induction before with
  | refl => exact after
  | tail _ step ih => exact ih (.again step after)

private def Invariant (m : Model.{u, v, w} Op) (graph : Graph Op carried sigs)
    (start : Tuple m.Val carried) : Marking m graph → Prop
  | .active input body =>
    ReflTransGen (fun i o => graph.body.run m i = bodyResult m true o) start input ∧
      ReflTransGen (RVSDG.Petri.Step m graph.body input) (RVSDG.Petri.initial m graph.body) body
  | .returned output => graph.Returns m start output

theorem sound (m : Model.{u, v, w} Op) (graph : Graph Op carried sigs)
    {input output : Tuple m.Val carried} (finishes : Finishes m graph input output) :
    graph.Returns m input output := by
  change ReflTransGen (Step m graph) (initial m graph input) (.returned output) at finishes
  suffices all : ∀ mark, ReflTransGen (Step m graph) (initial m graph input) mark →
      Invariant m graph input mark from all _ finishes
  intro mark steps
  induction steps with
  | refl => exact ⟨.refl, .refl⟩
  | tail _ step ih =>
    cases step with
    | inside inner => exact ⟨ih.1, ih.2.tail inner⟩
    | again completed =>
      have bodyRun := (RVSDG.Petri.finishes_iff m graph.body _ _).1 ⟨_, ih.2, completed⟩
      exact ⟨ih.1.tail bodyRun, .refl⟩
    | exit completed =>
      have bodyRun := (RVSDG.Petri.finishes_iff m graph.body _ _).1 ⟨_, ih.2, completed⟩
      exact prepend_repeats ih.1 (.stop bodyRun)

private theorem body_steps (m : Model.{u, v, w} Op) (graph : Graph Op carried sigs)
    {input : Tuple m.Val carried} {output : Tuple m.Val (BodyResults carried)}
    (returns : RVSDG.Petri.Finishes m graph.body input output) :
    ∃ body, ReflTransGen (Step m graph) (initial m graph input) (.active input body) ∧
      RVSDG.Petri.result m graph.body input body = some output := by
  obtain ⟨body, sequence, completed⟩ := returns
  exact ⟨body, sequence.lift (p := Step m graph) (Marking.active input) (fun _ _ => Step.inside),
    completed⟩

theorem complete (m : Model.{u, v, w} Op) (graph : Graph Op carried sigs)
    {input output : Tuple m.Val carried} (execution : graph.Returns m input output) :
    Finishes m graph input output := by
  induction execution with
  | stop last =>
    obtain ⟨_, steps, completed⟩ := body_steps m graph ((RVSDG.Petri.finishes_iff m graph.body _ _).2 last)
    exact steps.tail (.exit completed)
  | again first _ ih =>
    obtain ⟨_, steps, completed⟩ := body_steps m graph ((RVSDG.Petri.finishes_iff m graph.body _ _).2 first)
    exact (steps.tail (.again completed)).trans ih

theorem diverges_iff (m : Model.{u, v, w} Op) (graph : Graph Op carried sigs)
    (input : Tuple m.Val carried) : Diverges m graph input ↔ graph.Diverges m input := by
  constructor
  · rintro ⟨states, first, steps⟩
    exact ⟨states, first, fun n => (RVSDG.Petri.finishes_iff m graph.body _ _).1 (steps n)⟩
  · rintro ⟨states, first, steps⟩
    exact ⟨states, first, fun n => (RVSDG.Petri.finishes_iff m graph.body _ _).2 (steps n)⟩

theorem restart_after_body (m : Model.{u, v, w} Op) (graph : Graph Op carried sigs)
    {input next : Tuple m.Val carried}
    (returns : RVSDG.Petri.Finishes m graph.body input (bodyResult m true next)) :
    ∃ mark, ReflTransGen (Step m graph) (initial m graph input) mark ∧
      Step m graph mark (initial m graph next) := by
  obtain ⟨_, steps, completed⟩ := body_steps m graph returns
  exact ⟨_, steps, .again completed⟩

end Silmaril.SSA.RVSDG.Theta.Petri.Proofs
