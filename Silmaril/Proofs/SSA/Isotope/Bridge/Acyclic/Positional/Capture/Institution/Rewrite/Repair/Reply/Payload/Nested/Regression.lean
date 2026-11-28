module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Nested.Thms

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Nested

open Kleisli (value)
open LambdaSSA.Region (packedExitType)

private abbrev tail : List Sorts := [Bit]
private abbrev Packed := value (packedExitType (Bit :: tail))

private def terminal (result : Expr) : Arm (Bit :: tail) :=
  ⟨[false, true], ⟨0, rfl⟩, result⟩

private def sample (outerBound innerBound : Bool) (changedArm : Expr) : ProgramBody (Bit :: tail) :=
  let unchanged : Inner (Bit :: tail) := ⟨terminal .payload, terminal .payload⟩
  let edited : Inner (Bit :: tail) := ⟨terminal .payload, terminal changedArm⟩
  ⟨true, outerBound, .request [] false innerBound unchanged edited,
    .finish ⟨[], ⟨1, rfl⟩, .payload⟩⟩

private def source := sample true true .payload
private def direct := sample false false (.table false true)
private def changed := sample true true (.table false false)

-- Native replay changes both request forms and expands the retained bit
-- to its identity table under the second request and the final emits.
example : Derivable false (equation Bit tail source direct) :=
  derive_normal _ _ _ _ rfl

private noncomputable def observePair (p : ProgramBody (Bit :: tail)) (outer tag inner : Bool) : Set (Outcome Packed) :=
  afterPayload false tag inner (afterPayload p.request false outer (programOutcomes Bit tail p))

private theorem observe_sample (outerBound innerBound : Bool) (expr : Expr) (outer tag inner : Bool) :
    observePair (sample outerBound innerBound expr) outer tag inner =
      ((terminal (if tag && inner then expr else .payload)).normal.traceTree outer).outcomesWith
        Exits.Exit.packed := by
  unfold observePair
  rw [programAfterOuter]
  cases tag <;> cases inner <;>
    exact afterRequest Exits.Exit.packed false _ _ _ _

-- The outer right arm skips the second request and retains its original exit.
example (b : Bool) :
    afterPayload source.request true b (programOutcomes Bit tail source) =
      afterPayload changed.request true b (programOutcomes Bit tail changed) := by
  rw [programAfterOuter, programAfterOuter]
  rfl

-- On the outer left arm the programs agree on every pair other than
-- (outer true payload, inner right tag with true payload).
example (outer tag inner : Bool) (same : ¬ (outer = true ∧ tag = true ∧ inner = true)) :
    observePair source outer tag inner = observePair changed outer tag inner := by
  unfold source changed
  rw [observe_sample, observe_sample]
  cases outer <;> cases tag <;> cases inner <;>
    first | rfl | exact False.elim (same ⟨rfl, rfl, rfl⟩)

private def emitted : Log := FreeMonoid.of (.emit false) * FreeMonoid.of (.emit true)

private theorem source_final :
    observePair source true true true = {(.ok (Sum.inl (bit true) : Packed), emitted)} := by
  unfold source
  rw [observe_sample]
  change prepend (.emit false) '' (prepend (.emit true) '' {(.ok (Sum.inl (bit true) : Packed), 1)}) = _
  simp only [Set.image_singleton, prepend, mul_one, emitted]
  rfl

example : observePair changed true true true = {(.ok (Sum.inl (bit false) : Packed), emitted)} := by
  unfold changed
  rw [observe_sample]
  change prepend (.emit false) '' (prepend (.emit true) '' {(.ok (Sum.inl (bit false) : Packed), 1)}) = _
  simp only [Set.image_singleton, prepend, mul_one, emitted]
  rfl

set_option backward.isDefEq.respectTransparency false in
-- The observed path contains one outer reply pair and one inner reply pair,
-- followed by the two emits and the original exit with the retained bit.
example :
    (.ok (Sum.inl (bit true) : Packed), replyLog true false true * replyLog false true true * emitted) ∈
      programOutcomes Bit tail source := by
  have h : (.ok (Sum.inl (bit true) : Packed), emitted) ∈ observePair source true true true := by
    rw [source_final]
    rfl
  change prepend (.answer true false) (prepend (.answer true true)
    (prepend (.answer false true) (prepend (.answer false true)
      (.ok (Sum.inl (bit true) : Packed), emitted)))) ∈ programOutcomes Bit tail source at h
  simpa only [prepend, replyLog, mul_assoc] using h

example : ¬ (grammarRoom (Kleisli.J (m := Trace)) signature).Sat separator (equation Bit tail source changed) := by
  intro h
  cases (separator_sat_iff_normal _ _ _ _).mp h

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Nested
