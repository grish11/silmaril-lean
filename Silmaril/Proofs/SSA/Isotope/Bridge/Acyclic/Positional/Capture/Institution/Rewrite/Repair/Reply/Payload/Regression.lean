module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Thms

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

open Kleisli (value)
open LambdaSSA.Region (packedExitType)

private abbrev tail : List Sorts := [Bit]
private abbrev Packed := value (packedExitType (Bit :: tail))

private def left (result : Expr) : Arm (Bit :: tail) :=
  ⟨[false, true], ⟨0, rfl⟩, result⟩

private def right : Arm (Bit :: tail) :=
  ⟨[true], ⟨1, rfl⟩, .payload⟩

private def source : ProgramBody (Bit :: tail) := ⟨true, true, left .payload, right⟩
private def table : ProgramBody (Bit :: tail) := ⟨true, false, left (.table false true), right⟩
private def changed : ProgramBody (Bit :: tail) := ⟨true, true, left (.table false false), right⟩

-- The explicit identity table and the bound operand use different native terms.
example : Derivable false (equation Bit tail source table) :=
  derive_normal _ _ _ _ rfl

-- Both arms and both bit values are present in the model. The two programs
-- agree on every reply except the true payload of the left arm.
example (tag b : Bool) (same : tag = true ∨ b = false) :
    afterPayload true tag b (programOutcomes Bit tail source) =
      afterPayload true tag b (programOutcomes Bit tail changed) := by
  change afterPayload source.request tag b (programOutcomes Bit tail source) =
    afterPayload changed.request tag b (programOutcomes Bit tail changed)
  rw [programAfterPayload, programAfterPayload]
  rcases same with rfl | rfl
  · rfl
  · cases tag <;> rfl

private def effects : Log := FreeMonoid.of (.emit false) * FreeMonoid.of (.emit true)

example : afterPayload true false true (programOutcomes Bit tail source) =
    {(.ok (Sum.inl (bit true) : Packed), effects)} := by
  change afterPayload source.request false true (programOutcomes Bit tail source) = _
  rw [programAfterPayload]
  change prepend (.emit false) '' (prepend (.emit true) '' {(.ok (Sum.inl (bit true) : Packed), 1)}) = _
  simp only [Set.image_singleton, prepend, mul_one, effects]
  rfl

example : afterPayload true false true (programOutcomes Bit tail changed) =
    {(.ok (Sum.inl (bit false) : Packed), effects)} := by
  change afterPayload changed.request false true (programOutcomes Bit tail changed) = _
  rw [programAfterPayload]
  change prepend (.emit false) '' (prepend (.emit true) '' {(.ok (Sum.inl (bit false) : Packed), 1)}) = _
  simp only [Set.image_singleton, prepend, mul_one, effects]
  rfl

example : ¬ (grammarRoom (Kleisli.J (m := Trace)) signature).Sat separator (equation Bit tail source changed) := by
  intro h
  cases (separator_sat_iff_normal _ _ _ _).mp h

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
