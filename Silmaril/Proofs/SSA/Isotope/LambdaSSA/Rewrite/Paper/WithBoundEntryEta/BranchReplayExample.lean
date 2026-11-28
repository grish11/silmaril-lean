module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Branch.Example.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Branch.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.BranchReplayExample

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithBoundEntryEta.BranchReplay
open Paper.WithBoundEntryEta.BranchReplay.Example

theorem raw_typed : HasType [U] written [U] :=
  .let₁ .unit (.br (ℓ := 0) rfl (.op (.var (i := 1) rfl)))

theorem raw_not_guarded : ¬ ValueBranches [U] written [U] := by
  intro h
  cases h with
  | let₁ _ body =>
    cases body with
    | br _ term => cases term

theorem pullback_eq : Paper.WithBoundEntryEta.Eqv [U] written bound [U] := by
  obtain ⟨q, he, _, _, eq⟩ := bindAt_pullback site raw_typed replacement (s := boundComposite) rfl
  change some bound = some q at he
  cases Option.some.inj he
  exact eq

theorem normalized_eq : Paper.Eqv [U] written.bindBranchArguments bound.bindBranchArguments [U] :=
  bindAt_normalized site raw_typed rfl

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.BranchReplayExample
