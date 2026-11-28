module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Nested.Example.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Nested.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Comparison.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Normalization.Guarded.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Eta.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.NestedReplayExample

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithBoundEntryEta.NestedReplay
open Paper.WithBoundEntryEta.NestedReplay.Example
open Paper.WithBoundEntryEta.Generators.Example (Choice discriminator innerEntry innerRows nestedEntry)
open Paper.EntryLetObstruction.Destructure (U P labels rows entry reentered reentry_ne)
open SequencingObstruction (Instruction)

private theorem base_typed : HasType [Choice] (.cfg nestedEntry 2 outerRows) [U] := by
  have hd : Tm.HasType [Choice] discriminator Choice := .let₁ (.op .unit) (.var (i := 1) rfl)
  have entryType : HasType [Choice] innerEntry [Choice, U, P, U] :=
    .case hd (.br (ℓ := 0) rfl (.inl (.var rfl))) (.br (ℓ := 2) rfl (.var rfl))
  have innerType (j : Fin 1) : HasType [Choice, Choice] (innerRows j) [Choice, U, P, U] :=
    .case (.var (i := 0) rfl) (.br (ℓ := 1) rfl (.op (.var rfl))) (.br (ℓ := 2) rfl (.var rfl))
  have outerType (j : Fin 2) : HasType (labels j :: [Choice]) (outerRows j) [U, P, U] :=
    Fin.cases (.br (ℓ := 1) rfl (.pair (.var rfl) .unit))
      (fun _ => .case (.var (i := 1) rfl) (.br (ℓ := 2) rfl (.var rfl)) (.br (ℓ := 2) rfl .unit)) j
  exact .cfg labels (.cfg (fun _ => Choice) entryType innerType) outerType

private theorem original_typed : HasType [Choice] original [U] :=
  .let₁ .unit (base_typed.renameVars (Ren.wk [Choice] U))

private theorem original_move : hoistAt site original = some hoisted := by
  let innerHoisted : Region Instruction :=
    .cfg (innerEntry.lsubst (liftLSubstN 1 (cfgEntryContinuations outerRows))) 1
      (fun j => (innerRows j).lsubst (liftLSubstVars (liftLSubstN 1 (cfgEntryContinuations outerRows))))
  have root : hoistAt .here (.cfg nestedEntry 2 outerRows) = some innerHoisted := rfl
  change (hoistAt .here ((Region.cfg nestedEntry 2 outerRows).renameVars Nat.succ)).map
      (Region.let₁ .unit) = some hoisted
  rw [renameVars_eq_substVars, hoistAt_substVars, root]
  simp only [Option.map_some, hoisted, renameVars_eq_substVars, innerHoisted]

theorem composite_move :
    hoistAt site (original.substVars specialize) = some (hoisted.substVars specialize) := by
  rw [hoistAt_substVars, original_move]
  rfl

theorem pullback :
    HasType [Choice] hoisted [U] ∧ Paper.WithBoundEntryEta.Eqv [Choice] original hoisted [U] ∧
      HasType [U] (hoisted.substVars specialize) [U] := by
  obtain ⟨q, hq, _, htyped, eq⟩ := hoistAt_pullback site original_typed specialize composite_move
  rw [original_move] at hq
  cases Option.some.inj hq
  have values : ∀ ⦃i A⦄, At [Choice] i A → Tm.BranchValue [U] (specialize i) A := by
    intro i A hi
    cases i with
    | zero => cases Option.some.inj hi; exact .inl (.var rfl)
    | succ i => simp [At] at hi
  exact ⟨htyped, eq, htyped.substVars (fun _ _ hi => (values hi).hasType)⟩

theorem zeroInner_guards : ValueBranches [] zeroInnerOriginal [U] ∧ ValueBranches [] zeroInnerHoisted [U] := by
  have he := Paper.WithBoundEntryEta.Comparison.DestructureFixture.entry_typed
  have hr := Paper.WithBoundEntryEta.Comparison.DestructureFixture.rows_typed (Γ := [])
  have before : ValueBranches [] zeroInnerOriginal [U] :=
    .cfg labels (.cfg (Fin.elim0 : Fin 0 → Ty Empty) he (fun i => i.elim0)) hr
  exact ⟨before, (hoistAt_guarded .here before rfl).1⟩

theorem zeroInner_ne : ¬ Paper.WithEntryLet.Eqv [] zeroInnerOriginal zeroInnerHoisted [U] := by
  intro eq
  have he := Paper.WithBoundEntryEta.Comparison.DestructureFixture.entry_typed
  have ho := Paper.WithBoundEntryEta.Comparison.DestructureFixture.rows_typed (Γ := [])
  have left : Paper.WithEntryLet.Eqv [] zeroInnerOriginal (.cfg entry 2 rows) [U] :=
    .cfg labels (.paper (.cfgEta (.native (.base (.entry (.cfgZero he.hasType emptyInner))))))
      (fun j => .refl (ho j).hasType)
  have family := cfgEntryContinuations_hasType labels (fun j => (ho j).hasType)
  have right : Paper.WithEntryLet.Eqv [] zeroInnerHoisted (entry.lsubst (cfgEntryContinuations rows)) [U] :=
    .paper (.cfgEta (.native (.base (.entry (.cfgZero (he.hasType.lsubst family) _)))))
  have normalized : Paper.WithEntryLet.Eqv [] (entry.lsubst (cfgEntryContinuations rows)) reentered [U] :=
    .lsubstPost (.paper (.cfgEta (.native he.bindBranchArguments_equiv)))
      he he.hasType.bindBranchArguments family
  exact reentry_ne (left.symm.trans (eq.trans (right.trans normalized)))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.NestedReplayExample
