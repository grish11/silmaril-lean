module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Case.Example.Defs
import all Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SequencingObstruction.FlatPaper

/-! # Standard Paper separates the two case-entry representatives -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Sequencing

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.SequencingObstruction
open Paper.EntryLetObstruction (finish)
open Paper.EntryLetObstruction.Destructure (U)

/-- Use the same arity profile as the flat Paper observer. -/
private local instance : MarkArity where
  enabled n := decide (2 ≤ n)

open Paper.WithBoundEntryEta.Generators.Example (Choice) in
open Paper.WithBoundEntryEta.CaseReplay.Example (original hoisted) in
theorem caseEntry_ne : ¬ Paper.Eqv [Choice] original hoisted [U] := by
  intro eq
  let env : Env := fun _ => .inl .unit
  have he : EnvTyped [Choice] env := by
    intro i A hi
    cases i with
    | zero => cases Option.some.inj hi; exact .inl .unit
    | succ i => simp [At] at hi
  have before : observesFlat env original (finish true) :=
    execute_sound 4 _ env rfl
  have after : observesFlat env hoisted (finish false) :=
    execute_sound 4 _ env rfl
  have marked := (observesFlat_eq_of_paper eq env he (finish true)).mp before
  exact Bool.noConfusion (congrArg Exit.marked (observe_unique _ env marked after))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Sequencing
