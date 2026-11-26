module

public import Silmaril.Semantics.ITree.Trace.Finite.Defs
import Silmaril.Semantics.ITree.Trace.Thms
import Silmaril.Proofs.Semantics.ITree.Trace.Finite.Explore
import Silmaril.Proofs.Semantics.ITree.Trace.Finite.Observe

@[expose] public section

namespace Silmaril.Proofs.Semantics.Elgot.ITree.Finite

open Silmaril.Elgot.ITree Silmaril.Elgot.ITree.Finite

universe u
variable {Q Reply : Type} {R S T : Type u}

private theorem result_trace {tree : Tree (Event Q Reply) R} {run : S → Tree (Event Q Reply) R}
    {head : Head Q R S Reply} (observed : out tree = head.render run) (value : R) :
    HasTrace tree (.result value) ↔ head = .result value := by
  cases head <;> simp [HasTrace, observed, Head.render]

private theorem request_trace {tree : Tree (Event Q Reply) R} {run : S → Tree (Event Q Reply) R}
    {head : Head Q R S Reply} (observed : out tree = head.render run) (key : Q) :
    HasTrace tree (.request (.ask key)) ↔ ∃ next, head = .request key next := by
  cases head <;> simp [HasTrace, observed, Head.render, Visible.vis.injEq, Event.ask.injEq]

private theorem exchange_trace {tree : Tree (Event Q Reply) R} {run : S → Tree (Event Q Reply) R}
    {head : Head Q R S Reply} (observed : out tree = head.render run)
    (key : Q) (reply : Reply) (tail : Trace (Event Q Reply) R) :
    HasTrace tree (.exchange (.ask key) reply tail) ↔
      ∃ next, head = .request key next ∧ HasTrace (run (next reply)) tail := by
  cases head <;> simp [HasTrace, observed, Head.render, Visible.vis.injEq, Event.ask.injEq, Function.comp_def]

variable [DecidableEq S] [DecidableEq T] [DecidableEq Q] [DecidableEq R] [Fintype Reply]
  {runL : S → Tree (Event Q Reply) R} {runR : T → Tree (Event Q Reply) R}
  {headL : S → Head Q R S Reply} {headR : T → Head Q R T Reply}

private theorem refine_of_simulation (pairs : Finset (S × T))
    (observedL : ∀ s, out (runL s) = (headL s).render runL)
    (observedR : ∀ t, out (runR t) = (headR t).render runR)
    (closed : ∀ s t, (s, t) ∈ pairs → compatible pairs (headL s) (headR t) = true)
    {s : S} {t : T} (related : (s, t) ∈ pairs) :
    TraceLE (runL s) (runR t) := by
  intro trace
  induction trace generalizing s t with
  | «prefix» => intro _; trivial
  | result value =>
    intro seen
    have hl := (result_trace (observedL s) value).mp seen
    have allowed := closed s t related
    rw [hl] at allowed
    apply (result_trace (observedR t) value).mpr
    cases hr : headR t <;> simp_all [compatible]
  | request event =>
    cases event with
    | ask key =>
      intro seen
      obtain ⟨nextL, hl⟩ := (request_trace (observedL s) key).mp seen
      have allowed := closed s t related
      rw [hl] at allowed
      apply (request_trace (observedR t) key).mpr
      cases hr : headR t <;> simp_all [compatible]
  | exchange event reply tail ih =>
    cases event with
    | ask key =>
      intro seen
      obtain ⟨nextL, hl, suffix⟩ := (exchange_trace (observedL s) key reply tail).mp seen
      have allowed := closed s t related
      rw [hl] at allowed
      apply (exchange_trace (observedR t) key reply tail).mpr
      cases hr : headR t with
      | stop | result _ => simp [compatible, hr] at allowed
      | request k nextR =>
        have checks : key = k ∧ ∀ reply, (nextL reply, nextR reply) ∈ pairs := by
          simpa [compatible, hr] using allowed
        exact ⟨nextR, checks.1 ▸ rfl, ih (checks.2 reply) suffix⟩

private theorem simulation_of_refine (pairs : Finset (S × T))
    (observedL : ∀ s, out (runL s) = (headL s).render runL)
    (observedR : ∀ t, out (runR t) = (headR t).render runR)
    (included : ∀ s t, TraceLE (runL s) (runR t) → (s, t) ∈ pairs)
    (s : S) (t : T) (related : TraceLE (runL s) (runR t)) :
    compatible pairs (headL s) (headR t) = true := by
  cases hl : headL s with
  | stop => rfl
  | result value =>
    have seen := related _ ((result_trace (observedL s) value).mpr hl)
    have hr := (result_trace (observedR t) value).mp seen
    simp [compatible, hr]
  | request key nextL =>
    have seen := related _ ((request_trace (observedL s) key).mpr ⟨nextL, hl⟩)
    obtain ⟨nextR, hr⟩ := (request_trace (observedR t) key).mp seen
    have replies (reply : Reply) : (nextL reply, nextR reply) ∈ pairs := by
      apply included
      intro tail present
      have seen := related _ ((exchange_trace (observedL s) key reply tail).mpr ⟨nextL, hl, present⟩)
      obtain ⟨next, same, has⟩ := (exchange_trace (observedR t) key reply tail).mp seen
      rw [hr, Head.request.injEq] at same
      exact same.2 ▸ has
    simp [compatible, hr, replies]

theorem compare_exact (statesL : Finset S) (statesR : Finset T)
    (completeL : ∀ s, s ∈ statesL) (completeR : ∀ t, t ∈ statesR)
    (left : S → Step Q R S Reply) (right : T → Step Q R T Reply) (s : S) (t : T) :
    compare statesL statesR left right s t = true ↔ TraceLE (evaluate left s) (evaluate right t) := by
  let keep (pairs : Finset (S × T)) (p : S × T) :=
    compatible pairs (headFrom left statesL p.1) (headFrom right statesR p.2)
  let pairs := prune keep (statesL ×ˢ statesR)
  have spec := prune_spec keep (statesL ×ˢ statesR)
  have observeL := out_evaluate left statesL completeL
  have observeR := out_evaluate right statesR completeR
  change decide ((s, t) ∈ pairs) = true ↔ _
  rw [decide_eq_true_eq]
  refine ⟨refine_of_simulation pairs observeL observeR (fun l r => spec.2.1 (l, r)), ?_⟩
  refine spec.2.2 (fun p => TraceLE (evaluate left p.1) (evaluate right p.2)) ?_ ?_ (s, t)
  · intro p _
    exact Finset.mem_product.mpr ⟨completeL _, completeR _⟩
  · rintro candidates inside ⟨l, r⟩ related
    exact simulation_of_refine candidates observeL observeR (fun l r => inside (l, r)) l r related

end Silmaril.Proofs.Semantics.Elgot.ITree.Finite
