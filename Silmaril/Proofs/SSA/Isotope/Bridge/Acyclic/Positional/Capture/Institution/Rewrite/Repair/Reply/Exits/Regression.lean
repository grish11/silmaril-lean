module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Exits.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Thms

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Exits

open Kleisli (value)
open LambdaSSA.Region (packedExitType)

private abbrev U : Sorts := .unit
private abbrev tail : List Sorts := [U]

private def first : Exit (U :: tail) := ⟨0, PUnit.unit⟩
private def second : Exit (U :: tail) := ⟨1, PUnit.unit⟩

private def source : Tree (Exit (U :: tail)) :=
  .ask true true (.emit false (.ret first)) (.emit true (.ret second))

private def direct : Tree (Exit (U :: tail)) :=
  .ask true false (.emit false (.ret first)) (.emit true (.ret second))

private def swapped : Tree (Exit (U :: tail)) :=
  .ask true true (.emit false (.ret second)) (.emit true (.ret first))

example : Repaired false (equation U tail source direct) :=
  repaired_of_normal _ _ _ _ rfl

example : grammarCase (readGrammar (numberGrammar (equation U tail source direct))) =
    grammarCase (equation U tail source direct) :=
  grammarCase_roundTrip _

private abbrev Result := value (packedExitType (U :: tail))

-- The reply and emit are held fixed. The two observed unit values differ
-- by the physical nested coproduct tag for their outward slot.
example :
    afterReply true false (programOutcomes U tail source) =
      {(.ok (Sum.inl PUnit.unit : Result), FreeMonoid.of (.emit false))} := by
  rw [source, programAfterReply]
  simp only [Bool.false_eq_true, ite_false, programOutcomes_eq, Tree.normal, Normal.outcomesWith]
  rw [Set.image_singleton]
  rfl

example :
    afterReply true false (programOutcomes U tail swapped) =
      {(.ok (Sum.inr (Sum.inl PUnit.unit) : Result), FreeMonoid.of (.emit false))} := by
  rw [swapped, programAfterReply]
  simp only [Bool.false_eq_true, ite_false, programOutcomes_eq, Tree.normal, Normal.outcomesWith]
  rw [Set.image_singleton]
  rfl

example : ¬ (grammarRoom (Kleisli.J (m := Trace)) signature).Sat separator (equation U tail source swapped) := by
  intro h
  cases (separator_sat_iff_normal _ _ _ _).mp h

private abbrev pairTail : List Sorts := [.product U U]
private def pairExit : Exit (U :: pairTail) := ⟨1, (PUnit.unit, PUnit.unit)⟩

example : programOutcomes U pairTail (.ret pairExit) =
    {(.ok (Sum.inr (Sum.inl (PUnit.unit, PUnit.unit)) : value (packedExitType (U :: pairTail))), 1)} :=
  programOutcomes_eq _ _ _

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Exits
