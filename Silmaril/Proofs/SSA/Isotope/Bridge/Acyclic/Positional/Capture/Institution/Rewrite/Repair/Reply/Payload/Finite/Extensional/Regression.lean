module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Extensional.Thms

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.Extensional

open Isotope.LetCase.LocallyNameless (Tm)
open Kleisli (value)
open LambdaSSA.Region (packedExitType)

private abbrev tail : List Sorts := [Bit]
private abbrev Packed := value (packedExitType (Bit :: tail))

private def first : Position (Bit :: tail) := ⟨0, rfl⟩
private def second : Position (Bit :: tail) := ⟨1, rfl⟩

private def retReply {n : Nat} (pos : Position (Bit :: tail)) : Tree (Bit :: tail) (n + 1) :=
  .ret pos (.read 0)

private def left {n : Nat} : Tree (Bit :: tail) (n + 1) :=
  .emit false (retReply first)

private def right {n : Nat} : Tree (Bit :: tail) (n + 1) :=
  .emit true (retReply second)

private def guarded (i : Fin 2) (factored : Bool) : Source (Bit :: tail) 2 :=
  .common i ⟨true, factored, ⟨left, right, left, right⟩⟩

private def plain : Source (Bit :: tail) 2 :=
  .tree (.request true false left right)

private def changed : Source (Bit :: tail) 2 :=
  .common 1 ⟨true, true, ⟨left, right, .emit false (retReply second), right⟩⟩

private theorem guard_normal (i : Fin 2) (factored : Bool) (env : Assignment 2) :
    (guarded i factored).normal env = plain.normal env := by
  unfold guarded
  cases h : env i
  · simp only [Source.normal, commonNormal, h, Bool.false_eq_true, ite_false]
    rfl
  · simp only [Source.normal, commonNormal, h, ite_true]
    rfl

-- The native terms use different discriminators at their entry case.
example : ((guarded 1 false).operand (CommonRequest.bitSlots 2)).1 ≠
    (plain.operand (CommonRequest.bitSlots 2)).1 := by
  intro same
  cases (Tm.case.inj same).1

-- Extensional replay deletes a redundant guard and equates different tested slots.
example : Derivable false (equation Bit tail (guarded 1 false) plain) :=
  derive_normal Bit tail _ _ (guard_normal 1 false)

example : Derivable false (equation Bit tail (guarded 1 false) (guarded 0 true)) :=
  derive_normal Bit tail _ _ (fun env => (guard_normal 1 false env).trans (guard_normal 0 true env).symm)

-- On the true guard and left false reply, the programs have the same request,
-- effect, and returned bit. The changed continuation selects the second exit.
private theorem observe_true (p : Source (Bit :: tail) 2) (pos : Position (Bit :: tail))
    (h : p.normal (fun _ => true) =
      .request true (.emit false (.ret pos false)) (.emit false (.ret pos true))
        (.emit true (.ret second false)) (.emit true (.ret second true))) :
    afterPayload true false false (programOutcomes Bit tail p (fun _ => true)) =
      {(.ok (pos.result false).packed, FreeMonoid.of (.emit false))} := by
  rw [programOutcomes_eq, h]
  have reply := afterRequest Exits.Exit.packed true
    (fun b => (Path.emit false (.ret pos b)).traceTree)
    (fun b => (Path.emit true (.ret second b)).traceTree) false false
  change afterPayload true false false
    ((requestTree true (fun b => (Path.emit false (.ret pos b)).traceTree)
      (fun b => (Path.emit true (.ret second b)).traceTree)).outcomesWith Exits.Exit.packed) = _
  rw [reply]
  change prepend (.emit false) '' {(.ok (pos.result false).packed, 1)} = _
  simp only [Set.image_singleton, prepend, mul_one]

example :
    afterPayload true false false (programOutcomes Bit tail (guarded 0 true) (fun _ => true)) =
      {(.ok (Sum.inl (bit false) : Packed), FreeMonoid.of (.emit false))} :=
  observe_true (guarded 0 true) first rfl

example :
    afterPayload true false false (programOutcomes Bit tail changed (fun _ => true)) =
      {(.ok (Sum.inr (Sum.inl (bit false)) : Packed), FreeMonoid.of (.emit false))} :=
  observe_true changed second rfl

example : ¬ (grammarRoom (Kleisli.J (m := Trace)) signature).Sat separator
    (equation Bit tail (guarded 0 true) changed) := by
  intro sat
  have normal := (separator_sat_iff_normal Bit tail _ _).mp sat (fun _ => true)
  have pos := (Path.ret.inj (Path.emit.inj (Path.request.inj normal).2.1).2).1
  have atSlot := congrArg (fun p : Position (Bit :: tail) => p.1.val) pos
  contradiction

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.Extensional
