module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Generators.Example.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Generators.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Comparison.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.GeneratorExamples

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.Generators
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.Generators.Example
open Paper.EntryLetObstruction.Destructure (U P labels rows)

private theorem disc_typed : Tm.HasType [Choice] discriminator Choice :=
  .let₁ (.op .unit) (.var (i := 1) rfl)

theorem effectful_caseEntry :
    Extension.Eqv Candidate [Choice] (.cfg (.case discriminator leftArm rightArm) 2 rows)
      (.case discriminator (.cfg leftArm 2 (weakenRows rows)) (.cfg rightArm 2 (weakenRows rows))) [U] :=
  candidate_caseEntry labels disc_typed (.br (ℓ := 0) rfl (.var rfl)) (.br (ℓ := 1) rfl (.var rfl))
    WithBoundEntryEta.Comparison.DestructureFixture.rows_typed

private theorem innerEntry_typed : HasType [Choice] innerEntry [Choice, U, P, U] :=
  .case disc_typed (.br (ℓ := 0) rfl (.inl (.var rfl))) (.br (ℓ := 2) rfl (.var rfl))

private theorem innerRows_typed (i : Fin 1) : HasType [Choice, Choice] (innerRows i) [Choice, U, P, U] :=
  .case (.var (i := 0) rfl)
    (.br (ℓ := 1) rfl (.op (.var rfl))) (.br (ℓ := 2) rfl (.var rfl))

theorem nested_hoist :
    WithBoundEntryEta.Eqv [Choice] (.cfg nestedEntry 2 rows)
      (.cfg (innerEntry.lsubst (liftLSubstN 1 (cfgEntryContinuations rows))) 1
        (fun j => (innerRows j).lsubst (liftLSubstVars (liftLSubstN 1 (cfgEntryContinuations rows))))) [U] :=
  nested (fun _ => Choice) labels innerEntry_typed innerRows_typed
    (fun j => (WithBoundEntryEta.Comparison.DestructureFixture.rows_typed j).hasType)

theorem nested_reentry :
    WithBoundEntryEta.Generators.Eqv [Choice] (.cfg nestedEntry 2 rows)
      (nestedEntry.bindBranchArguments.lsubst (cfgEntryContinuations rows)) [U] :=
  WithBoundEntryEta.Generators.reentry labels (.cfg (fun _ => Choice) innerEntry_typed innerRows_typed)
    (fun j => (WithBoundEntryEta.Comparison.DestructureFixture.rows_typed j).hasType)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.GeneratorExamples
