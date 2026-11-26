module

public import Silmaril.Semantics.ITree.Trace.Finite.Defs
import Silmaril.Semantics.ITree.Trace.Thms
import Silmaril.Proofs.Semantics.ITree.Trace.Finite.Explore
import Silmaril.Proofs.Semantics.ITree.Trace.Finite.Observe

@[expose] public section

namespace Silmaril.Proofs.Semantics.Elgot.ITree.Finite

open Silmaril.Elgot.ITree Silmaril.Elgot.ITree.Finite

universe u v
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

variable [DecidableEq Q] [DecidableEq R]
  [∀ key, Fintype (Reply key)]
  {runL : S → Tree (Event Q Reply) R} {runR : T → Tree (Event Q Reply) R}
  {headL : S → Head Q R S Reply} {headR : T → Head Q R T Reply}

private theorem request_compatible (follow : ∀ key, Reply key → S → T → Prop)
    [∀ key reply s t, Decidable (follow key reply s t)] (key : Q) (nextL : Reply key → S)
    (right : Head Q R T Reply) (allowed : compatibleUsing follow (.request key nextL) right = true) :
    ∃ nextR, right = .request key nextR ∧ ∀ reply, follow key reply (nextL reply) (nextR reply) := by
  cases right with
  | stop | result _ => simp [compatibleUsing] at allowed
  | request actual nextR =>
    by_cases same : key = actual
    · subst actual
      exact ⟨nextR, rfl, by simpa [compatibleUsing] using allowed⟩
    · simp [compatibleUsing, same] at allowed

variable {H : Type v} (step : Handler H (Event Q Reply))
  (related : H → S → T → Prop) (follow : H → ∀ key, Reply key → S → T → Prop)
  [∀ h key reply s t, Decidable (follow h key reply s t)]
  (follows : ∀ h key reply s t, follow h key reply s t ↔
    ∀ h', step ⟨_, .ask key⟩ h reply h' → related h' s t)

include follows in
private theorem refine_of_simulation
    (observedL : ∀ s, out (runL s) = (headL s).render runL)
    (observedR : ∀ t, out (runR t) = (headR t).render runR)
    (closed : ∀ h s t, related h s t → compatibleUsing (follow h) (headL s) (headR t) = true)
    {h : H} {s : S} {t : T} (pair : related h s t) :
    ∀ trace, HandledTrace step h (runL s) trace → HasTrace (runR t) trace := by
  intro trace
  induction trace generalizing h s t with
  | «prefix» => intro _; trivial
  | result value =>
    intro seen
    have hl := (result_trace (observedL s) value).mp seen.1
    have allowed := closed h s t pair
    rw [hl] at allowed
    apply (result_trace (observedR t) value).mpr
    cases hr : headR t <;> simp_all [compatibleUsing]
  | request event =>
    cases event with
    | ask key =>
      intro seen
      obtain ⟨nextL, hl⟩ := (request_trace (observedL s) key).mp seen.1
      have allowed := closed h s t pair
      rw [hl] at allowed
      obtain ⟨nextR, hr, _⟩ := request_compatible (follow h) key nextL (headR t) allowed
      exact (request_trace (observedR t) key).mpr ⟨nextR, hr⟩
  | exchange event reply tail ih =>
    cases event with
    | ask key =>
      intro seen
      obtain ⟨nextL, hl, suffix⟩ := (exchange_trace (observedL s) key reply tail).mp seen.1
      have allowed := closed h s t pair
      rw [hl] at allowed
      obtain ⟨nextR, hr, checks⟩ := request_compatible (follow h) key nextL (headR t) allowed
      obtain ⟨h', admitted, rest⟩ := seen.2
      have next := (follows h key reply _ _).mp (checks reply) h' admitted
      exact (exchange_trace (observedR t) key reply tail).mpr ⟨nextR, hr, ih next ⟨suffix, rest⟩⟩

include follows in
private theorem simulation_of_refine
    (observedL : ∀ s, out (runL s) = (headL s).render runL)
    (observedR : ∀ t, out (runR t) = (headR t).render runR)
    (included : ∀ h s t, (∀ trace, HandledTrace step h (runL s) trace →
      HasTrace (runR t) trace) → related h s t)
    (h : H) (s : S) (t : T)
    (pair : ∀ trace, HandledTrace step h (runL s) trace → HasTrace (runR t) trace) :
    compatibleUsing (follow h) (headL s) (headR t) = true := by
  cases hl : headL s with
  | stop => rfl
  | result value =>
    have seen := pair _ ⟨(result_trace (observedL s) value).mpr hl, trivial⟩
    have hr := (result_trace (observedR t) value).mp seen
    simp [compatibleUsing, hr]
  | request key nextL =>
    have seen := pair _ ⟨(request_trace (observedL s) key).mpr ⟨nextL, hl⟩, trivial⟩
    obtain ⟨nextR, hr⟩ := (request_trace (observedR t) key).mp seen
    have replies (reply : Reply key) : follow h key reply (nextL reply) (nextR reply) := by
      apply (follows h key reply _ _).mpr
      intro h' allowed
      apply included
      intro tail present
      have seen := pair _ ⟨(exchange_trace (observedL s) key reply tail).mpr ⟨nextL, hl, present.1⟩,
        ⟨h', allowed, present.2⟩⟩
      exact (exchange_at nextR (hr ▸ observedR t) reply tail).mp seen
    simpa [compatibleUsing, hr] using replies

variable [DecidableEq S] [DecidableEq T]

omit [DecidableEq S] [DecidableEq T] [DecidableEq Q] [∀ key, Fintype (Reply key)] in
private theorem stateless_follow (admits : ∀ key, Reply key → Bool)
    (pairs : Finset (S × T)) (h : Unit) (key : Q) (reply : Reply key) (s : S) (t : T) :
    (admits key reply = true → (s, t) ∈ pairs) ↔
      ∀ h', replyHandler admits ⟨_, .ask key⟩ h reply h' → (s, t) ∈ pairs :=
  ⟨fun yes _ => yes, fun yes => yes ()⟩

variable (admits : ∀ key, Reply key → Bool)

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
  refine ⟨refine_of_simulation _ _ _ (stateless_follow admits pairs)
    observeL observeR (fun _ l r => spec.2.1 (l, r)) (h := ()), ?_⟩
  refine spec.2.2 (fun p => ∀ trace, HandledTrace (replyHandler admits) () (evaluate left p.1) trace →
    HasTrace (evaluate right p.2) trace) ?_ ?_ (s, t)
  · intro p _
    exact Finset.mem_product.mpr ⟨completeL _, completeR _⟩
  · rintro candidates inside ⟨l, r⟩ related
    exact simulation_of_refine _ _ _ (stateless_follow admits candidates) observeL observeR
      (fun h l r good => by cases h; exact inside (l, r) good) () l r related

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

omit [DecidableEq S] [DecidableEq T] [DecidableEq Q] [∀ key, Fintype (Reply key)] in
private theorem stateful_follow [DecidableEq H] (advance : H → ∀ key, Reply key → Option H)
    (pairs : Finset ((S × T) × H)) (h : H) (key : Q) (reply : Reply key) (s : S) (t : T) :
    handlerSuccessor pairs s t (advance h key reply) ↔
      ∀ h', statefulReplyHandler advance ⟨_, .ask key⟩ h reply h' → ((s, t), h') ∈ pairs := by
  cases next : advance h key reply <;> simp [statefulReplyHandler, next, handlerSuccessor]

theorem compareWithHandler_exact [DecidableEq H] (advance : H → ∀ key, Reply key → Option H)
    (statesL : Finset S) (statesR : Finset T) (statesH : Finset H)
    (completeL : ∀ s, s ∈ statesL) (completeR : ∀ t, t ∈ statesR) (completeH : ∀ h, h ∈ statesH)
    (left : S → Step Q R S Reply) (right : T → Step Q R T Reply) (s : S) (t : T) (h : H) :
    compareWithHandler advance statesL statesR statesH left right s t h = true ↔
      ∀ trace, HandledTrace (statefulReplyHandler advance) h (evaluate left s) trace →
        HasTrace (evaluate right t) trace := by
  let keep (pairs : Finset ((S × T) × H)) (p : (S × T) × H) :=
    compatibleUsing (fun key reply l r => handlerSuccessor pairs l r (advance p.2 key reply))
      (headFrom left statesL p.1.1) (headFrom right statesR p.1.2)
  let candidates := (statesL ×ˢ statesR) ×ˢ statesH
  let pairs := prune keep candidates
  have spec := prune_spec keep candidates
  have observeL := out_evaluate left statesL completeL
  have observeR := out_evaluate right statesR completeR
  change decide (((s, t), h) ∈ pairs) = true ↔ _
  rw [decide_eq_true_eq]
  refine ⟨refine_of_simulation _ _ _ (stateful_follow advance pairs) observeL observeR
    (fun h l r => spec.2.1 ((l, r), h)), ?_⟩
  refine spec.2.2 (fun p => ∀ trace, HandledTrace (statefulReplyHandler advance) p.2 (evaluate left p.1.1) trace →
    HasTrace (evaluate right p.1.2) trace) ?_ ?_ ((s, t), h)
  · intro p _
    exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨completeL _, completeR _⟩, completeH _⟩
  · rintro remaining inside ⟨⟨l, r⟩, h⟩ good
    exact simulation_of_refine _ _ _ (stateful_follow advance remaining) observeL observeR
      (fun h l r => inside ((l, r), h)) h l r good

end Silmaril.Proofs.Semantics.Elgot.ITree.Finite
