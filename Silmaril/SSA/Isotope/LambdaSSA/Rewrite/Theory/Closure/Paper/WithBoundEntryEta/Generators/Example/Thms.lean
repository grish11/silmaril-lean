module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Generators.Example.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.GeneratorExamples

/-! # Effectful case entry and nested CFG re-entry -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.Generators.Example

open Paper.EntryLetObstruction.Destructure (U rows)

/-- #4152 supplies the discriminator bind needed to push a guarded table
into the arms of this computed case. -/
theorem effectful_caseEntry :
    Extension.Eqv Candidate [Choice] (.cfg (.case discriminator leftArm rightArm) 2 rows)
      (.case discriminator (.cfg leftArm 2 (weakenRows rows)) (.cfg rightArm 2 (weakenRows rows))) [U] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.GeneratorExamples.effectful_caseEntry

/-- The inner label stays local, with both outer labels routed to the
outer re-entry table. -/
theorem nested_hoist :
    WithBoundEntryEta.Eqv [Choice] (.cfg nestedEntry 2 rows)
      (.cfg (innerEntry.lsubst (liftLSubstN 1 (cfgEntryContinuations rows))) 1
        (fun j => (innerRows j).lsubst (liftLSubstVars (liftLSubstN 1 (cfgEntryContinuations rows))))) [U] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.GeneratorExamples.nested_hoist

/-- The structural generators also bind the raw instruction argument in
the inner row before redirecting its exit. -/
theorem nested_reentry :
    Eqv [Choice] (.cfg nestedEntry 2 rows) (nestedEntry.bindBranchArguments.lsubst (cfgEntryContinuations rows)) [U] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.GeneratorExamples.nested_reentry

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.Generators.Example
