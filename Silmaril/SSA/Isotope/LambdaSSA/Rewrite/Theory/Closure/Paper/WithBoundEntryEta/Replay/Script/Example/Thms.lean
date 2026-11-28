module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Script.Example.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.ScriptReplayExample

/-! # Three addressed generators below a binder -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.ScriptReplay.Example

open CaseReplay.Example (specialize)
open Generators.Example (Choice)
open Paper.EntryLetObstruction.Destructure (U)

theorem specialized_run : run moves (source.substVars specialize) = some (target.substVars specialize) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.ScriptReplayExample.specialized_run

/-- Both traces keep the exact exit type and execute the same addresses
after the captured sum is specialized to a left injection. -/
theorem replay :
    Trace [Choice] [U] moves source target ∧
    Trace [U] [U] moves (source.substVars specialize) (target.substVars specialize) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.ScriptReplayExample.replay

/-- Substitution can make the two case tables identical. The substituted
region has a typed predecessor under the forward action, while the
original region has no literal predecessor at that address. -/
theorem inverse_obstruction :
    HasType [U, U] inverseTarget [U] ∧
    Trace [] [U] [.caseEntry .here] closedPredecessor (inverseTarget.substVars forgetCaptures) ∧
    ¬ ∃ q, run [.caseEntry .here] q = some inverseTarget :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.ScriptReplayExample.inverse_obstruction

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.ScriptReplay.Example
