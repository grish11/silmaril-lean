module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Square.Example.Defs
import all Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SequencingObstruction.FlatPaper

/-! # The two original composites have different local transfer marks -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Sequencing

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.SequencingObstruction
open Paper.EntryLetObstruction (discardInput)
open Paper.WithEntryLet.OperandExample (Bit)
open Paper.WithBoundEntryEta.SquareReplay.Example (writtenFlat hoisted)

private local instance : MarkArity where
  enabled n := decide (2 ≤ n)

theorem squareReplay_ne :
    ¬ Paper.Eqv [Bit] (writtenFlat.substVars discardInput) (hoisted.substVars discardInput) [Bit] := by
  intro eq
  let env : Env := fun _ => .inl .unit
  have he : EnvTyped [Bit] env := by
    intro i A hi
    cases i with
    | zero => cases Option.some.inj hi; exact .inl .unit
    | succ i => simp [At] at hi
  let marked : Paper.EntryLetObstruction.Observation := ⟨0, .inr .unit, true, true⟩
  let unmarked : Paper.EntryLetObstruction.Observation := ⟨0, .inr .unit, true, false⟩
  have before : observesFlat env (writtenFlat.substVars discardInput) marked :=
    execute_sound 8 _ env rfl
  have after : observesFlat env (hoisted.substVars discardInput) unmarked :=
    execute_sound 8 _ env rfl
  have observed := (observesFlat_eq_of_paper eq env he marked).mp before
  exact Bool.noConfusion (congrArg Exit.marked (observe_unique _ env observed after))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Sequencing
