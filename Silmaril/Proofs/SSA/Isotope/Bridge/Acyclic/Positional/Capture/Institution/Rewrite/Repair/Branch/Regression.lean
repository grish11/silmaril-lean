module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Branch.Model.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Thms

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Branch

open Sequence (Sorts value run signature traceAlgebra)
open LetIter.Semantics.Categorical (boundEnv)

private abbrev exits : List Sorts := [.unit]

private def guarded : ProgramBody :=
  ⟨.known false (.emit false (.emit true .returnUnit)) (.emit true (.stop false true)),
   .known true (.emit false .returnUnit) (.emit true (.stop true true))⟩

private def writtenDirectly : ProgramBody :=
  ⟨.body (.emit false (.emit true .returnUnit)), .body (.emit true (.stop true false))⟩

-- Both literal guards disappear, including their unselected effectful code.
-- The live fault is written with the other empty-elimination orientation.
example : Repaired false (equation exits guarded writtenDirectly) :=
  (repaired_iff_normal _ _ _).mpr rfl

example : grammarCase (readGrammar (numberGrammar (equation exits guarded writtenDirectly))) =
    grammarCase (equation exits guarded writtenDirectly) :=
  grammarCase_roundTrip _

private def leftRight : ProgramBody :=
  ⟨.body (.emit false (.emit true .returnUnit)), .body (.emit true (.emit false .returnUnit))⟩

private def rightLeft : ProgramBody := ⟨leftRight.right, leftRight.left⟩

private noncomputable def input (tag : value Input) :=
  boundEnv value (β := inputContext) (PUnit.unit, tag)

-- Both arms return unit at the same outward position. Their reversed
-- effect words make a swap observable at either constructor.
example (tag : value Input) :
    run (leftRight.program exits).toLetCase.2 (input tag) ≠
      run (rightLeft.program exits).toLetCase.2 (input tag) := by
  rw [input, leftRight.run_input, rightLeft.run_input]
  cases tag <;> intro h <;> cases Sequence.Normal.observe_injective _ h

example :
    ¬ ((LetCase.inst (Ctx.nil : Ctx Empty Sorts)).obj signature).Sat traceAlgebra
      (grammarCase (equation exits leftRight rightLeft)) := by
  intro h
  have left := congrArg Prod.fst ((traceSat_iff_normal _ _ _).mp h)
  cases left

example : ¬ (grammarRoom Sequence.traceJ signature).Sat Sequence.validatedTraceModel
    (equation exits leftRight rightLeft) := by
  intro sat
  have h := (validatedTrace_sat_iff_repaired _ _ _).mp sat
  have left := congrArg Prod.fst ((repaired_iff_normal _ _ _).mp h)
  cases left

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Branch
