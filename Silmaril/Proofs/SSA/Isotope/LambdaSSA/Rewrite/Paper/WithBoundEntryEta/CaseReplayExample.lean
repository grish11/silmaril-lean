module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Case.Example.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Case.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Comparison.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.CaseReplayExample

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithBoundEntryEta.CaseReplay
open Paper.WithBoundEntryEta.CaseReplay.Example
open Paper.WithBoundEntryEta.Generators.Example (Choice discriminator)
open Paper.EntryLetObstruction.Destructure (U labels)

private theorem original_typed : HasType [Choice] original [U] :=
  .cfg labels (.case
    (.let₁ (.op .unit) (.var (i := 1) rfl) : Tm.HasType [Choice] discriminator Choice)
    (.br (ℓ := 0) rfl (.var rfl)) (.br (ℓ := 1) rfl (.var rfl)))
    (fun j => (Paper.WithBoundEntryEta.Comparison.DestructureFixture.rows_typed j).hasType)

theorem exact_move : Paper.WithBoundEntryEta.Eqv [Choice] original hoisted [U] :=
  (hoistAt_exact .here original_typed rfl).2

private theorem binder_move : hoistAt site (underBinder original) = some (underBinder hoisted) := by
  have root : hoistAt .here original = some hoisted := rfl
  change (hoistAt .here (original.renameVars Nat.succ)).map (Region.let₁ .unit) = _
  rw [renameVars_eq_substVars, hoistAt_substVars, root]
  simp only [Option.map_some, underBinder, renameVars_eq_substVars]

theorem composite_move :
    hoistAt site ((underBinder original).substVars specialize) =
      some ((underBinder hoisted).substVars specialize) := by
  rw [hoistAt_substVars, binder_move]
  rfl

theorem pullback :
    Paper.WithBoundEntryEta.Eqv [Choice] (underBinder original) (underBinder hoisted) [U] ∧
    HasType [U] ((underBinder hoisted).substVars specialize) [U] := by
  have typed : HasType [Choice] (underBinder original) [U] :=
    .let₁ .unit (original_typed.renameVars (Ren.wk [Choice] U))
  obtain ⟨q, hq, _, htyped, eq⟩ := hoistAt_pullback site typed specialize composite_move
  rw [binder_move] at hq
  cases Option.some.inj hq
  have values : ∀ ⦃i A⦄, At [Choice] i A → Tm.BranchValue [U] (specialize i) A := by
    intro i A hi
    cases i with
    | zero => cases Option.some.inj hi; exact .inl (.var rfl)
    | succ i => simp [At] at hi
  exact ⟨eq, htyped.substVars (fun _ _ hi => (values hi).hasType)⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.CaseReplayExample
