module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Thms

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite

open Kleisli (value)
open LambdaSSA.Region (packedExitType)

private abbrev tail : List Sorts := [Bit]
private abbrev Packed := value (packedExitType (Bit :: tail))

private def first : Position (Bit :: tail) := ⟨0, rfl⟩
private def second : Position (Bit :: tail) := ⟨1, rfl⟩

private def fixture (bound : Bool) (e : Expr 3) : Tree (Bit :: tail) 0 :=
  .request true bound
    (.request false bound (.ret second (.literal false))
      (.request true bound (.emit false (.emit true (.ret first e))) (.ret second (.literal true))))
    (.ret second (.literal true))

private def source := fixture true (.read 2)
private def direct := fixture false (Expr.quote 3 (fun env => env 2))
private def changed := fixture true (.split (.read 1) (.split (.read 0) (.literal false)))

-- The oldest bit stays live through two later bound requests and two emits.
example : Derivable false (equation Bit tail source direct) := by
  apply derive_normal
  have table : (Expr.quote 3 (fun env => env 2)).eval = (Expr.read (2 : Fin 3)).eval :=
    funext (Expr.quote_eval 3 (fun env => env 2))
  simp only [source, direct, fixture, Tree.normal, table]

private noncomputable def selected (p : Tree (Bit :: tail) 0) (a b c : Bool) : Set (Outcome Packed) :=
  afterPayload true false c (afterPayload false true b (afterPayload true false a (programOutcomes Bit tail p)))

private theorem selected_fixture (bound : Bool) (e : Expr 3) (a b c : Bool) :
    selected (fixture bound e) a b c =
      (Normal.emit false (.emit true (.ret first e.eval))).outcomes
        (((Assignment.push (n := 0) Fin.elim0 a).push b).push c) := by
  unfold selected
  rw [programOutcomes_eq]
  simp only [fixture, Tree.normal, Normal.afterRequest, Bool.false_eq_true, ite_false, ite_true]

-- Of the eight assignments along this path, only three true payloads
-- change the return. Both programs retain the same request and exit tags.
example (a b c : Bool) (same : ¬ (a = true ∧ b = true ∧ c = true)) :
    selected source a b c = selected changed a b c := by
  unfold source changed
  rw [selected_fixture, selected_fixture]
  cases a <;> cases b <;> cases c <;>
    first | rfl | exact False.elim (same ⟨rfl, rfl, rfl⟩)

private def emitted : Log := FreeMonoid.of (.emit false) * FreeMonoid.of (.emit true)

private theorem source_final :
    selected source true true true = {(.ok (Sum.inl (bit true) : Packed), emitted)} := by
  unfold source
  rw [selected_fixture]
  change prepend (.emit false) '' (prepend (.emit true) '' {(.ok (Sum.inl (bit true) : Packed), 1)}) = _
  simp only [Set.image_singleton, prepend, mul_one, emitted]
  rfl

example : selected changed true true true = {(.ok (Sum.inl (bit false) : Packed), emitted)} := by
  unfold changed
  rw [selected_fixture]
  change prepend (.emit false) '' (prepend (.emit true) '' {(.ok (Sum.inl (bit false) : Packed), 1)}) = _
  simp only [Set.image_singleton, prepend, mul_one, emitted]
  rfl

set_option backward.isDefEq.respectTransparency false in
example :
    (.ok (Sum.inl (bit true) : Packed),
      replyLog true false true * replyLog false true true * replyLog true false true * emitted) ∈
      programOutcomes Bit tail source := by
  have h : (.ok (Sum.inl (bit true) : Packed), emitted) ∈ selected source true true true := by
    rw [source_final]
    rfl
  change prepend (.answer true false) (prepend (.answer true true)
    (prepend (.answer false true) (prepend (.answer false true)
      (prepend (.answer true false) (prepend (.answer true true)
        (.ok (Sum.inl (bit true) : Packed), emitted)))))) ∈ programOutcomes Bit tail source at h
  simpa only [prepend, replyLog, mul_assoc] using h

example : ¬ (grammarRoom (Kleisli.J (m := Trace)) signature).Sat separator (equation Bit tail source changed) := by
  intro sat
  have normal := (separator_sat_iff_normal _ _ _ _).mp sat
  have first := (Normal.request.inj normal).2.1
  have second := (Normal.request.inj first).2.2
  have third := (Normal.request.inj second).2.1
  have effects := (Normal.emit.inj (Normal.emit.inj third).2).2
  have table := (Normal.ret.inj effects).2
  have bad := congrFun table (fun _ => true)
  contradiction

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite
