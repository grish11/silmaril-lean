module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Case.Example.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.CaseReplayExample
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SequencingObstruction.CaseEntry

/-! # Case entry below a binder and the standard Paper boundary -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.CaseReplay.Example

open Generators.Example (Choice)
open Paper.EntryLetObstruction.Destructure (U)

theorem exact_move : WithBoundEntryEta.Eqv [Choice] original hoisted [U] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.CaseReplayExample.exact_move

/-- The same non-root site succeeds after specializing the captured sum
to a constructor containing a variable. -/
theorem composite_move :
    hoistAt site ((underBinder original).substVars specialize) =
      some ((underBinder hoisted).substVars specialize) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.CaseReplayExample.composite_move

theorem pullback :
    WithBoundEntryEta.Eqv [Choice] (underBinder original) (underBinder hoisted) [U] ∧
    HasType [U] ((underBinder hoisted).substVars specialize) [U] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.CaseReplayExample.pullback

/-- The left input makes two local transfers after the effect inside the
original table. The hoisted table starts after that effect. The flat
diagnostic separates these fixed representatives in standard Paper. -/
theorem paper_ne : ¬ Paper.Eqv [Choice] original hoisted [U] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Sequencing.caseEntry_ne

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.CaseReplay.Example
