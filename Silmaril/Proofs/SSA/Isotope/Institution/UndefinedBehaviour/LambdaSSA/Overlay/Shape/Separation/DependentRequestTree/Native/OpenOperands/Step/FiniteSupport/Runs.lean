module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Thms

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open CFG.Dependent (Packet)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits)
open Syntax (Payload StateReply StatePrimitives)

universe u v w

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R : List Syntax.Ty}
  {σ : Type v} {τ : Type w}
  {g : Table S R} {caller : Payload (R.get g.entry)} {prim : StatePrimitives Φ σ}
  {p : Packet R} {s initial : σ} {rows : List (RunRow Φ σ)} {stop : RunStop σ}

private theorem terminal_run {o : Outcome Exits.length Unit σ}
    (observed : (g.feedback caller prim (blockPoint p s)).Ordinary (Feedback.external R Exits o)) :
    ∃ rows stop, FiniteRun g caller prim p s rows stop := by
  cases head : g.head caller p with
  | exit j selected => exact ⟨_, _, .exit head⟩
  | diverge => exact ⟨_, _, .silent head⟩
  | request f arg next =>
    cases reply : prim f arg s with
    | fault t => exact ⟨_, _, .fault head reply⟩
    | diverge => exact ⟨_, _, .diverge head reply⟩
    | ret value t =>
      let q := replyDestination f next value
      have execution : (g.head caller p).execute prim s = .repeat q t := by
        rw [head, Head.execute, reply]
        rfl
      have step := (g.feedback_step_iff caller prim p s (blockPoint q t)).mpr ⟨q, t, execution, rfl⟩
      have raw := g.feedback_step caller prim p s
      rw [execution] at raw
      have same : Feedback.external R Exits o =
          Outcome.ret (Feedback.internal R Exits q.1) q.2.val t := by
        simpa [raw, Behaviour.possible, StateTransition.routed] using observed.2
      have terminal : g.feedback caller prim (blockPoint p s) = WithTop.some {Feedback.external R Exits o} :=
        raw.trans (congrArg (fun out => WithTop.some ({out} : Set _)) same.symm)
      exact (no_step_of_terminal terminal step).elim

theorem of_feedback_finite {o : Outcome Exits.length Unit σ}
    (finite : Feedback.Finite (g.feedback caller prim) (blockPoint p s) o) :
    ∃ rows stop, FiniteRun g caller prim p s rows stop := by
  obtain ⟨last, reach, observed⟩ := finite
  have follow {first} (path : Feedback.Reaches (g.feedback caller prim) first last) :
      ∀ p s, first = blockPoint p s → ∃ rows stop, FiniteRun g caller prim p s rows stop := by
    induction path using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro p s atBlock
      exact terminal_run (atBlock ▸ observed)
    | @head start mid step _ ih =>
      intro p s atBlock
      subst start
      obtain ⟨next, t, execution, atNext⟩ := (g.feedback_step_iff caller prim p s mid).mp step
      obtain ⟨rows, stop, rest⟩ := ih next t atNext
      cases head : g.head caller p with
      | exit | diverge =>
        rw [head, Head.execute] at execution
        cases execution
      | request f arg route =>
        rw [head, Head.execute] at execution
        cases reply : prim f arg s with
        | ret value final =>
          rw [reply] at execution
          obtain ⟨rfl, rfl⟩ := StateTransition.repeat.inj execution
          exact ⟨_, _, .repeat head reply rest⟩
        | fault | diverge =>
          rw [reply] at execution
          cases execution
  exact follow reach p s rfl

theorem records (run : FiniteRun g caller prim p s rows stop) :
    ∀ r ∈ rows, prim r.op r.arg r.incoming = r.answer := by
  induction run with
  | exit | silent => simp
  | «repeat» _ reply _ ih =>
    intro r listed
    rcases List.mem_cons.mp listed with rfl | inTail
    · exact reply
    · exact ih r inTail
  | fault _ reply =>
    intro r listed
    obtain rfl := List.mem_singleton.mp listed
    exact reply
  | diverge _ reply =>
    intro r listed
    obtain rfl := List.mem_singleton.mp listed
    exact reply

theorem covered (run : FiniteRun g caller prim p s rows stop)
    (support : RunSupport σ initial) (start : s ∈ support.values)
    (returned : rows.filterMap RunRow.returned? ⊆ support.values) :
    (∀ r ∈ rows, r.incoming ∈ support.values) ∧
      ∀ t, stop.final? = some t → t ∈ support.values := by
  induction run with
  | exit =>
    refine ⟨by simp, ?_⟩
    intro t h
    exact (Option.some.inj h) ▸ start
  | silent => simp [RunStop.final?]
  | @«repeat» p s f arg next value t rows stop _ _ _ ih =>
    have mid : t ∈ support.values := returned (List.mem_cons_self ..)
    obtain ⟨queries, final⟩ := ih mid (fun _ mem => returned (List.mem_cons_of_mem _ mem))
    refine ⟨?_, final⟩
    intro r listed
    rcases List.mem_cons.mp listed with rfl | inTail
    · exact start
    · exact queries r inTail
  | fault =>
    refine ⟨?_, ?_⟩
    · intro r listed
      obtain rfl := List.mem_singleton.mp listed
      exact start
    · intro _ same
      obtain rfl := Option.some.inj same
      exact returned (List.mem_cons_self ..)
  | diverge =>
    refine ⟨?_, by simp [RunStop.final?]⟩
    intro r listed
    obtain rfl := List.mem_singleton.mp listed
    exact start

/-- The typed derivation is sufficient to replay both the original and
a coded interpreter. The rest of the interpreter is irrelevant. -/
theorem replay (run : FiniteRun g caller prim p s rows stop)
    (code : σ → τ) (other : StatePrimitives Φ τ)
    (realizes : ∀ r ∈ rows, other r.op r.arg (code r.incoming) = r.answer.mapState code) :
    g.observeAt caller other p (code s) = (stop.mapState code).behaviour := by
  induction run with
  | exit head | silent head => rw [g.observe_state_step, head]; rfl
  | @«repeat» p s f arg next value t rows stop head _ _ ih =>
    have reply := realizes ⟨f, arg, s, .ret value t⟩ (List.mem_cons_self ..)
    rw [g.observe_state_step, head, Head.execute, reply]
    exact ih (fun r mem => realizes r (List.mem_cons_of_mem _ mem))
  | @fault p s f arg next t head _ =>
    have reply := realizes ⟨f, arg, s, .fault t⟩ (List.mem_singleton_self _)
    rw [g.observe_state_step, head, Head.execute, reply]
    rfl
  | @diverge p s f arg next head _ =>
    have reply := realizes ⟨f, arg, s, .diverge⟩ (List.mem_singleton_self _)
    rw [g.observe_state_step, head, Head.execute, reply]
    rfl

theorem observes (run : FiniteRun g caller prim p s rows stop) :
    g.observeAt caller prim p s = stop.behaviour := by
  have same : (stop.mapState id).behaviour = stop.behaviour := by cases stop <;> rfl
  refine (replay run id prim (fun r mem => (records run r mem).trans ?_)).trans same
  cases r.answer <;> rfl

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport
