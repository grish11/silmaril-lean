module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Thms

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite

open Kleisli (value)
open LambdaSSA.Region (packedExitType)

private abbrev tail : List Sorts := [Bit]
private abbrev Packed := value (packedExitType (Bit :: tail))

private def first : Position (Bit :: tail) := ⟨0, rfl⟩
private def second : Position (Bit :: tail) := ⟨1, rfl⟩

private def guard (test : Fin 2) (bound : Bool) (kept : Expr 2) : Tree (Bit :: tail) 2 :=
  .testRequest test false bound bound
    (.emit false (.ret first kept)) (.ret first (.read 0))
    (.emit true (.ret second kept)) (.ret second (.read 0))

private def fixture (test : Fin 2) (bound : Bool) (kept : Expr 2) : Tree (Bit :: tail) 0 :=
  .request true bound
    (.request false bound (.ret first (.literal false)) (guard test bound kept))
    (.ret second (.literal true))

private def source := fixture 1 true (.read 1)
private def direct := fixture 1 false (Expr.quote 2 (fun env => env 1))
private def latest := fixture 0 true (.read 1)

-- Replay normalizes both guarded requests under the fresh unit binder.
-- The other prior reply remains live and is returned at the chosen exit.
example : Derivable false (equation Bit tail source direct) := by
  apply derive_normal
  have table : (Expr.quote 2 (fun env => env 1)).eval = (Expr.read (1 : Fin 2)).eval :=
    funext (Expr.quote_eval 2 (fun env => env 1))
  simp only [source, direct, fixture, guard, Tree.normal, table]

private def replies (older newer : Bool) : Assignment 2 :=
  (Assignment.push (n := 0) Fin.elim0 older).push newer

private noncomputable def atGuard (p : Tree (Bit :: tail) 0) (older newer : Bool) :
    Set (Outcome Packed) :=
  afterPayload false true newer (afterPayload true false older (programOutcomes Bit tail p))

private theorem atGuard_fixture (test : Fin 2) (bound : Bool) (kept : Expr 2) (older newer : Bool) :
    atGuard (fixture test bound kept) older newer = (guard test bound kept).normal.outcomes (replies older newer) := by
  unfold atGuard
  rw [programOutcomes_eq]
  simp only [fixture, Tree.normal, Normal.afterRequest, Bool.false_eq_true, ite_false, ite_true, replies]

private theorem chosen (test : Fin 2) (bound : Bool) (kept : Expr 2) (older newer : Bool) :
    afterPayload (if replies older newer test then true else false) false true
        (atGuard (fixture test bound kept) older newer) =
      (if replies older newer test then Normal.emit true (.ret second kept.eval)
        else Normal.emit false (.ret first kept.eval)).outcomes
          (((replies older newer).without test).push true) := by
  rw [atGuard_fixture]
  exact Normal.afterTestRequest test false
    (.emit false (.ret first kept.eval)) (.ret first (Expr.read 0).eval)
    (.emit true (.ret second kept.eval)) (.ret second (Expr.read 0).eval)
    (replies older newer) false true

-- Holding the newer reply fixed, the older bit changes the next request
-- label, the emit, and the ordered exit tag. The returned bit is the same.
private theorem oldest_false :
    afterPayload false false true (atGuard source false true) =
      {(.ok (Sum.inl (bit true) : Packed), FreeMonoid.of (.emit false))} := by
  change afterPayload (if replies false true (1 : Fin 2) then true else false) false true
    (atGuard (fixture 1 true (.read 1)) false true) = _
  rw [chosen]
  change prepend (.emit false) '' {(.ok (Sum.inl (bit true) : Packed), 1)} = _
  simp only [Set.image_singleton, prepend, mul_one]
  rfl

example :
    afterPayload true false true (atGuard source true true) =
      {(.ok (Sum.inr (Sum.inl (bit true)) : Packed), FreeMonoid.of (.emit true))} := by
  change afterPayload (if replies true true (1 : Fin 2) then true else false) false true
    (atGuard (fixture 1 true (.read 1)) true true) = _
  rw [chosen]
  change prepend (.emit true) '' {(.ok (Sum.inr (Sum.inl (bit true)) : Packed), 1)} = _
  simp only [Set.image_singleton, prepend, mul_one]
  rfl

example :
    afterPayload true false true (atGuard latest false true) =
      {(.ok (Sum.inr (Sum.inl (bit false)) : Packed), FreeMonoid.of (.emit true))} := by
  change afterPayload (if replies false true (0 : Fin 2) then true else false) false true
    (atGuard (fixture 0 true (.read 1)) false true) = _
  rw [chosen]
  change prepend (.emit true) '' {(.ok (Sum.inr (Sum.inl (bit false)) : Packed), 1)} = _
  simp only [Set.image_singleton, prepend, mul_one]
  rfl

-- This path executes just its one selected third request.
set_option backward.isDefEq.respectTransparency false in
example :
    (.ok (Sum.inl (bit true) : Packed),
      replyLog true false false * replyLog false true true * replyLog false false true *
        FreeMonoid.of (.emit false)) ∈ programOutcomes Bit tail source := by
  have h : (.ok (Sum.inl (bit true) : Packed), FreeMonoid.of (.emit false)) ∈
      afterPayload false false true (atGuard source false true) := by
    rw [oldest_false]
    rfl
  change prepend (.answer true false) (prepend (.answer true false)
    (prepend (.answer false true) (prepend (.answer false true)
      (prepend (.answer false false) (prepend (.answer false true)
        (.ok (Sum.inl (bit true) : Packed), FreeMonoid.of (.emit false))))))) ∈
    programOutcomes Bit tail source at h
  simpa only [prepend, replyLog, mul_assoc] using h

example : ¬ (grammarRoom (Kleisli.J (m := Trace)) signature).Sat separator
    (equation Bit tail source latest) := by
  intro sat
  have normal := (separator_sat_iff_normal _ _ _ _).mp sat
  have first := (Normal.request.inj normal).2.1
  have second := (Normal.request.inj first).2.2
  have guardSlot := (Normal.testRequest.inj second).1
  contradiction

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite
