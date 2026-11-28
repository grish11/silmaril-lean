module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Branch.Example.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.BranchReplayExample

/-! # Addressed branch binding through one captured variable -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.BranchReplay.Example

/-- The addressed branch is exactly typed with its captured variable. -/
theorem raw_typed : HasType [U] written [U] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.BranchReplayExample.raw_typed

theorem raw_not_guarded : ¬ ValueBranches [U] written [U] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.BranchReplayExample.raw_not_guarded

/-- The constructor replacement changes the captured operand to unit. -/
theorem composite_move :
    bindAt site (written.substVars replacement) = some boundComposite :=
  rfl

/-- Pullback restores the actual operand and the original exact context. -/
theorem pullback_eq : WithBoundEntryEta.Eqv [U] written bound [U] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.BranchReplayExample.pullback_eq

theorem normalized_eq : Paper.Eqv [U] written.bindBranchArguments bound.bindBranchArguments [U] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.BranchReplayExample.normalized_eq

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.BranchReplay.Example
