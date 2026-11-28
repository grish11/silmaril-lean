module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Nested.Example.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.NestedReplayExample

/-! # Exact addressed replay and a separate native obstruction -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.NestedReplay.Example

open Paper.EntryLetObstruction.Destructure (U)
open Generators.Example (Choice)

/-- Specializing the captured sum still leaves the hoist at the same
address, below the retained value binder. -/
theorem composite_move :
    hoistAt site (original.substVars specialize) = some (hoisted.substVars specialize) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.NestedReplayExample.composite_move

/-- The local Choice label and both differently typed outer labels route
at the original type and at its constructor specialization. -/
theorem pullback :
    HasType [Choice] hoisted [U] ∧ WithBoundEntryEta.Eqv [Choice] original hoisted [U] ∧
      HasType [U] (hoisted.substVars specialize) [U] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.NestedReplayExample.pullback

/-- The separate obstruction is itself a successful addressed hoist. -/
theorem zeroInner_move : hoistAt .here zeroInnerOriginal = some zeroInnerHoisted := rfl

theorem zeroInner_guards : ValueBranches [] zeroInnerOriginal [U] ∧ ValueBranches [] zeroInnerHoisted [U] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.NestedReplayExample.zeroInner_guards

/-- Eliminating the zero-row inner tables reduces the native comparison
to the separated computed-destructuring example. -/
theorem zeroInner_ne : ¬ WithEntryLet.Eqv [] zeroInnerOriginal zeroInnerHoisted [U] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.NestedReplayExample.zeroInner_ne

theorem zeroInner_native_ne : ¬ Paper.Eqv [] zeroInnerOriginal zeroInnerHoisted [U] :=
  fun h => zeroInner_ne (.paper h)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.NestedReplay.Example
