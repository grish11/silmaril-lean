module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Case.Inverse.Example.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Script.Example.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.CaseInverseExample

/-! # Backward case replay below an enclosing binder -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.CaseReplay.InverseExample

open CaseReplay.Example (site specialize)
open Generators.Example (Choice)
open Paper.EntryLetObstruction.Destructure (U)

/-- The same two differently typed rows are available before either arm
payload is bound. The second row reads the retained sum. -/
theorem commonTable : CommonTableAt [Choice] [U] site hoisted :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.CaseInverseExample.commonTable

/-- The specialized backward step recovers the original exact predecessor
below the let and its opt-in equality in the reverse direction. -/
theorem backward :
    hoistAt site (original.substVars specialize) = some (hoisted.substVars specialize) ∧
    HasType [Choice] original [U] ∧ WithBoundEntryEta.Eqv [Choice] hoisted original [U] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.CaseInverseExample.backward

/-- The original from the unconditional inverse obstruction has no
common-table witness. -/
theorem unequalTables_ineligible :
    ¬ CommonTableAt [U, U] [U] .here WithBoundEntryEta.ScriptReplay.Example.inverseTarget :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.CaseInverseExample.unequalTables_ineligible

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.CaseReplay.InverseExample
