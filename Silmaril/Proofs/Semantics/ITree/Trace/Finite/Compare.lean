module

public import Silmaril.Semantics.ITree.Trace.Finite.Defs
import Silmaril.Semantics.ITree.Trace.Thms
import Silmaril.Proofs.Semantics.ITree.Trace.Finite.Explore
import Silmaril.Proofs.Semantics.ITree.Trace.Finite.Observe

@[expose] public section

namespace Silmaril.Proofs.Semantics.Elgot.ITree.Finite

open Silmaril.Elgot.ITree Silmaril.Elgot.ITree.Finite

universe u
variable {Q : Type} {Reply : Q → Type} {R S T : Type u}

theorem result_trace {tree : Tree (Event Q Reply) R} {run : S → Tree (Event Q Reply) R}
    {head : Head Q R S Reply} (observed : out tree = head.render run) (value : R) :
    HasTrace tree (.result value) ↔ head = .result value := by
  cases head <;> simp [HasTrace, observed, Head.render]

private def visibleKey : Visible (Event Q Reply) R (Tree (Event Q Reply) R) → Option Q
  | .ret _ => none
  | .vis (.ask key) _ => some key

theorem request_trace {tree : Tree (Event Q Reply) R} {run : S → Tree (Event Q Reply) R}
    {head : Head Q R S Reply} (observed : out tree = head.render run) (key : Q) :
    HasTrace tree (.request (.ask key)) ↔ ∃ next, head = .request key next := by
  cases head with
  | stop | result _ => simp [HasTrace, observed, Head.render]
  | request actual next =>
    constructor
    · rintro ⟨_, root⟩
      rw [observed, Head.render] at root
      have same : actual = key :=
        Option.some.inj (congrArg (visibleKey (R := R) (Reply := Reply)) (Part.some_injective root))
      subst actual
      exact ⟨next, rfl⟩
    · rintro ⟨next', found⟩
      exact ⟨run ∘ next', by rw [observed, found, Head.render]⟩

theorem exchange_at {X : Type u} {run : X → Tree (Event Q Reply) R}
    {tree : Tree (Event Q Reply) R} {key : Q} (next : Reply key → X)
    (observed : out tree = (Head.request key next).render run)
    (reply : Reply key) (tail : Trace (Event Q Reply) R) :
    HasTrace tree (.exchange (.ask key) reply tail) ↔ HasTrace (run (next reply)) tail := by
  have root : tree = vis (.ask key) (run ∘ next) := by
    apply out_injective
    rw [observed, Head.render, out_vis]
  rw [root, hasTrace_vis_exchange_iff]
  rfl

private theorem exchange_trace {tree : Tree (Event Q Reply) R} {run : S → Tree (Event Q Reply) R}
    {head : Head Q R S Reply} (observed : out tree = head.render run)
    (key : Q) (reply : Reply key) (tail : Trace (Event Q Reply) R) :
    HasTrace tree (.exchange (.ask key) reply tail) ↔
      ∃ next, head = .request key next ∧ HasTrace (run (next reply)) tail := by
  have follow (next : Reply key → S) (found : head = .request key next) :
      HasTrace tree (.exchange (.ask key) reply tail) ↔ HasTrace (run (next reply)) tail := by
    exact exchange_at next (found ▸ observed) reply tail
  constructor
  · intro seen
    have pending : HasTrace tree (.request (.ask key)) := by
      obtain ⟨k, root, _⟩ := seen
      exact ⟨k, root⟩
    obtain ⟨next, found⟩ := (request_trace observed key).mp pending
    exact ⟨next, found, (follow next found).mp seen⟩
  · rintro ⟨next, found, suffix⟩
    exact (follow next found).mpr suffix

private theorem replay_exchange (admits : ∀ key, Reply key → Bool) (key : Q) (reply : Reply key)
    (tail : Trace (Event Q Reply) R) :
    Replay (replyHandler admits) () (.exchange (.ask key) reply tail) ↔
      admits key reply = true ∧ Replay (replyHandler admits) () tail :=
  ⟨fun ⟨(), allowed, rest⟩ => ⟨allowed, rest⟩, fun ⟨allowed, rest⟩ => ⟨(), allowed, rest⟩⟩

variable [DecidableEq S] [DecidableEq T] [DecidableEq Q] [DecidableEq R]
  [∀ key, Fintype (Reply key)]
  {runL : S → Tree (Event Q Reply) R} {runR : T → Tree (Event Q Reply) R}
  {headL : S → Head Q R S Reply} {headR : T → Head Q R T Reply}

variable (admits : ∀ key, Reply key → Bool)

private theorem request_compatible (pairs : Finset (S × T)) (key : Q) (nextL : Reply key → S)
    (right : Head Q R T Reply) (allowed : compatibleUnder admits pairs (.request key nextL) right = true) :
    ∃ nextR, right = .request key nextR ∧ ∀ reply, admits key reply = true → (nextL reply, nextR reply) ∈ pairs := by
  cases right with
  | stop | result _ => simp [compatibleUnder] at allowed
  | request actual nextR =>
    by_cases same : key = actual
    · subst actual
      exact ⟨nextR, rfl, by simpa [compatibleUnder] using allowed⟩
    · simp [compatibleUnder, same] at allowed

private theorem refine_of_simulation (pairs : Finset (S × T))
    (observedL : ∀ s, out (runL s) = (headL s).render runL)
    (observedR : ∀ t, out (runR t) = (headR t).render runR)
    (closed : ∀ s t, (s, t) ∈ pairs → compatibleUnder admits pairs (headL s) (headR t) = true)
    {s : S} {t : T} (related : (s, t) ∈ pairs) :
    ∀ trace, HandledTrace (replyHandler admits) () (runL s) trace → HasTrace (runR t) trace := by
  intro trace
  induction trace generalizing s t with
  | «prefix» => intro _; trivial
  | result value =>
    intro seen
    have hl := (result_trace (observedL s) value).mp seen.1
    have allowed := closed s t related
    rw [hl] at allowed
    apply (result_trace (observedR t) value).mpr
    cases hr : headR t <;> simp_all [compatibleUnder]
  | request event =>
    cases event with
    | ask key =>
      intro seen
      obtain ⟨nextL, hl⟩ := (request_trace (observedL s) key).mp seen.1
      have allowed := closed s t related
      rw [hl] at allowed
      obtain ⟨nextR, hr, _⟩ := request_compatible admits pairs key nextL (headR t) allowed
      exact (request_trace (observedR t) key).mpr ⟨nextR, hr⟩
  | exchange event reply tail ih =>
    cases event with
    | ask key =>
      intro seen
      obtain ⟨nextL, hl, suffix⟩ := (exchange_trace (observedL s) key reply tail).mp seen.1
      have allowed := closed s t related
      rw [hl] at allowed
      obtain ⟨nextR, hr, checks⟩ := request_compatible admits pairs key nextL (headR t) allowed
      have ⟨admitted, rest⟩ := (replay_exchange admits key reply tail).mp seen.2
      exact (exchange_trace (observedR t) key reply tail).mpr
        ⟨nextR, hr, ih (checks reply admitted) ⟨suffix, rest⟩⟩

private theorem simulation_of_refine (pairs : Finset (S × T))
    (observedL : ∀ s, out (runL s) = (headL s).render runL)
    (observedR : ∀ t, out (runR t) = (headR t).render runR)
    (included : ∀ s t, (∀ trace, HandledTrace (replyHandler admits) () (runL s) trace →
      HasTrace (runR t) trace) → (s, t) ∈ pairs)
    (s : S) (t : T) (related : ∀ trace, HandledTrace (replyHandler admits) () (runL s) trace →
      HasTrace (runR t) trace) :
    compatibleUnder admits pairs (headL s) (headR t) = true := by
  cases hl : headL s with
  | stop => rfl
  | result value =>
    have seen := related _ ⟨(result_trace (observedL s) value).mpr hl, trivial⟩
    have hr := (result_trace (observedR t) value).mp seen
    simp [compatibleUnder, hr]
  | request key nextL =>
    have seen := related _ ⟨(request_trace (observedL s) key).mpr ⟨nextL, hl⟩, trivial⟩
    obtain ⟨nextR, hr⟩ := (request_trace (observedR t) key).mp seen
    have replies (reply : Reply key) (allowed : admits key reply = true) : (nextL reply, nextR reply) ∈ pairs := by
      apply included
      intro tail present
      have seen := related _ ⟨(exchange_trace (observedL s) key reply tail).mpr ⟨nextL, hl, present.1⟩,
        (replay_exchange admits key reply tail).mpr ⟨allowed, present.2⟩⟩
      obtain ⟨next, same, has⟩ := (exchange_trace (observedR t) key reply tail).mp seen
      rw [hr, Head.request.injEq] at same
      exact (eq_of_heq same.2) ▸ has
    simpa [compatibleUnder, hr] using replies

theorem compareUnder_exact (statesL : Finset S) (statesR : Finset T)
    (completeL : ∀ s, s ∈ statesL) (completeR : ∀ t, t ∈ statesR)
    (left : S → Step Q R S Reply) (right : T → Step Q R T Reply) (s : S) (t : T) :
    compareUnder admits statesL statesR left right s t = true ↔
      ∀ trace, HandledTrace (replyHandler admits) () (evaluate left s) trace → HasTrace (evaluate right t) trace := by
  let keep (pairs : Finset (S × T)) (p : S × T) :=
    compatibleUnder admits pairs (headFrom left statesL p.1) (headFrom right statesR p.2)
  let pairs := prune keep (statesL ×ˢ statesR)
  have spec := prune_spec keep (statesL ×ˢ statesR)
  have observeL := out_evaluate left statesL completeL
  have observeR := out_evaluate right statesR completeR
  change decide ((s, t) ∈ pairs) = true ↔ _
  rw [decide_eq_true_eq]
  refine ⟨refine_of_simulation admits pairs observeL observeR (fun l r => spec.2.1 (l, r)), ?_⟩
  refine spec.2.2 (fun p => ∀ trace, HandledTrace (replyHandler admits) () (evaluate left p.1) trace →
    HasTrace (evaluate right p.2) trace) ?_ ?_ (s, t)
  · intro p _
    exact Finset.mem_product.mpr ⟨completeL _, completeR _⟩
  · rintro candidates inside ⟨l, r⟩ related
    exact simulation_of_refine admits candidates observeL observeR (fun l r => inside (l, r)) l r related

theorem compare_exact (statesL : Finset S) (statesR : Finset T)
    (completeL : ∀ s, s ∈ statesL) (completeR : ∀ t, t ∈ statesR)
    (left : S → Step Q R S Reply) (right : T → Step Q R T Reply) (s : S) (t : T) :
    compare statesL statesR left right s t = true ↔ TraceLE (evaluate left s) (evaluate right t) := by
  rw [Finite.compare, compareUnder_exact _ _ _ completeL completeR]
  refine ⟨fun included trace seen => included trace ⟨seen, ?_⟩, fun included trace seen => included trace seen.1⟩
  clear included seen
  induction trace with
  | «prefix» | request _ | result _ => trivial
  | exchange event reply tail ih =>
    cases event with
    | ask key => exact ⟨(), rfl, ih⟩

end Silmaril.Proofs.Semantics.Elgot.ITree.Finite
