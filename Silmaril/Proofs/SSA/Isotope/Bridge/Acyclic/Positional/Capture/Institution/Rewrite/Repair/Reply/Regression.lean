module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Model.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Thms

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply

private abbrev exits : List Sorts := [.unit]

private def leftWritten : Tree :=
  .emit false (.ask true true .returnUnit (.stop false true))

private def leftDirect : Tree :=
  .emit false (.ask true false .returnUnit (.stop false false))

private def source : Tree := .ask false true leftWritten (.emit true (.stop true true))

private def canonical : Tree := .ask false false leftDirect (.emit true (.stop true false))

private def changed : Tree := .ask false false leftDirect (.emit false (.stop true false))

example : Repaired false (equation exits source canonical) :=
  repaired_of_normal _ _ _ rfl

example : grammarCase (readGrammar (numberGrammar (equation exits source canonical))) =
    grammarCase (equation exits source canonical) :=
  grammarCase_roundTrip _

example : afterReply false false (source.programOutcomes exits) =
    afterReply false false (changed.programOutcomes exits) := by
  simp only [source, changed, programAfterReply, Bool.false_eq_true, ite_false]
  exact (programOutcomes_iff_normal _ _ _).mpr rfl

example : afterReply false true (source.programOutcomes exits) ≠
    afterReply false true (changed.programOutcomes exits) := by
  simp only [source, changed, programAfterReply, ite_true]
  intro h
  cases (programOutcomes_iff_normal _ _ _).mp h

example : ¬ (grammarRoom (Kleisli.J (m := Trace)) signature).Sat separator (equation exits source changed) := by
  intro h
  cases (separator_sat_iff_normal _ _ _).mp h

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply
