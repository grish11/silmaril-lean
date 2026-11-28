module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.CommonRequest.Thms

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.CommonRequest

open Kleisli (value)
open LambdaSSA.Region (packedExitType)

private abbrev tail : List Sorts := [Bit]
private abbrev Packed := value (packedExitType (Bit :: tail))

private def first : Position (Bit :: tail) := ⟨0, rfl⟩
private def second : Position (Bit :: tail) := ⟨1, rfl⟩

private def test : Fin 2 := 1

private def arms : Arms (Bit :: tail) 1 :=
  ⟨.emit false (.ret first (.read 1)), .ret first (.read 0),
    .emit true (.ret second (.read 1)), .ret second (.read 0)⟩

private def split : Source (Bit :: tail) 1 := ⟨true, false, arms⟩
private def shared : Source (Bit :: tail) 1 := ⟨true, true, arms⟩
private def changed : Source (Bit :: tail) 1 :=
  ⟨true, true, { arms with trueLeft := .emit true (.ret first (.read 1)) }⟩

private def assignment (guard : Bool) : Assignment 2 :=
  (Assignment.push (n := 0) Fin.elim0 guard).push true

example : Derivable false (equation Bit tail test split shared) :=
  derive_normal Bit tail test split shared rfl

private theorem after_reply (p : Source (Bit :: tail) 1) (guard right b : Bool) :
    afterPayload p.request right b (programOutcomes Bit tail test p (assignment guard)) =
      (if guard then (if right then p.normal.arms.trueRight else p.normal.arms.trueLeft)
        else (if right then p.normal.arms.falseRight else p.normal.arms.falseLeft)).outcomes
          (((assignment guard).without test).push b) := by
  rw [programOutcomes_eq]
  exact p.normal.afterRequest test (assignment guard) right b

-- For the same request and reply, the branches return the untested slot
-- at different positions even though the two positions have the same type.
example :
    afterPayload true false false (programOutcomes Bit tail test shared (assignment false)) =
      {(.ok (Sum.inl (bit true) : Packed), FreeMonoid.of (.emit false))} := by
  change afterPayload shared.request false false (programOutcomes Bit tail test shared (assignment false)) = _
  rw [after_reply]
  change prepend (.emit false) '' {(.ok (Sum.inl (bit true) : Packed), 1)} = _
  simp only [Set.image_singleton, prepend, mul_one]
  rfl

example :
    afterPayload true false false (programOutcomes Bit tail test shared (assignment true)) =
      {(.ok (Sum.inr (Sum.inl (bit true)) : Packed), FreeMonoid.of (.emit true))} := by
  change afterPayload shared.request false false (programOutcomes Bit tail test shared (assignment true)) = _
  rw [after_reply]
  change prepend (.emit true) '' {(.ok (Sum.inr (Sum.inl (bit true)) : Packed), 1)} = _
  simp only [Set.image_singleton, prepend, mul_one]
  rfl

-- The other reply tag returns its own payload, independent of the retained bit.
example :
    afterPayload true true false (programOutcomes Bit tail test split (assignment true)) =
      {(.ok (Sum.inr (Sum.inl (bit false)) : Packed), 1)} := by
  change afterPayload split.request true false (programOutcomes Bit tail test split (assignment true)) = _
  rw [after_reply]
  rfl

-- The factored term has exactly one recorded reply on each path.
example :
    programOutcomes Bit tail test shared (assignment true) =
      ({(.ok (Sum.inr (Sum.inl (bit true)) : Packed), replyLog true false false * FreeMonoid.of (.emit true))} ∪
        {(.ok (Sum.inr (Sum.inl (bit true))), replyLog true false true * FreeMonoid.of (.emit true))}) ∪
      ({(.ok (Sum.inr (Sum.inl (bit false))), replyLog true true false)} ∪
        {(.ok (Sum.inr (Sum.inl (bit true))), replyLog true true true)}) := by
  rw [programOutcomes_eq]
  change (requestTree true
    (fun _ => Reply.Normal.emit true (.ret (second.result true)))
    (fun b => Reply.Normal.ret (second.result b))).outcomesWith Exits.Exit.packed = _
  simp only [requestTree, Reply.Normal.outcomesWith, Set.image_union, Set.image_singleton, prepend, mul_one,
    replyLog, mul_assoc]
  rfl

example : ¬ (grammarRoom (Kleisli.J (m := Trace)) signature).Sat separator
    (equation Bit tail test split changed) := by
  intro sat
  have normal := (separator_sat_iff_normal Bit tail test split changed).mp sat
  have arm := congrArg (fun p : NormalSource (Bit :: tail) 1 => p.arms.trueLeft) normal
  have position := (Normal.ret.inj (Normal.emit.inj arm).2).1
  have slot := congrArg (fun p : Position (Bit :: tail) => p.1.val) position
  contradiction

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.CommonRequest
