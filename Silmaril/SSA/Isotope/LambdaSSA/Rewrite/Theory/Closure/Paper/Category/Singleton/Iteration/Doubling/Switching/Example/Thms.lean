module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Doubling.Switching.Example.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SwitchingDoublingExample

/-! # Short-circuiting and observable order in the two-step restriction -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.SwitchingExample

open CategoryTheory CategoryTheory.Limits
open Silmaril.Elgot.ITree
open Semantics.Interaction

local notation "E" => Event Op Empty

theorem ordered_typed : ValueBranches [Flag] orderedOutcome [U, PairTy] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SwitchingDoublingExample.ordered_typed

theorem actual_left : stateLeft ≫ doubled = ofRegion outcomeTyped ≫ coprod.inl :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SwitchingDoublingExample.actual_left

theorem right_repeat : flagRight ≫ right = ofRegion (requestTyped .second) ≫ flagRight ≫ coprod.inr :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SwitchingDoublingExample.right_repeat

theorem iterates_agree : iterate doubled = iterate step :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SwitchingDoublingExample.iterates_agree

/-- The left restrictions of both actual iterates use the same written
answer, which `orderedOutcome` decodes to its ordered exits. -/
theorem left_iterates :
    stateLeft ≫ iterate doubled = ofRegion outcomeTyped ∧
    stateLeft ≫ iterate step = ofRegion outcomeTyped :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SwitchingDoublingExample.left_iterates

theorem immediate_exit :
    region (F := E) Semantics.Interaction.request (fun _ => .inl .unit) orderedOutcome =
      ret (0, .unit) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SwitchingDoublingExample.immediate_exit

theorem two_leg_exit :
    region (F := E) Semantics.Interaction.request (fun _ => .inr .unit) orderedOutcome =
      vis (.call .first .unit) (fun _ =>
        vis (.call .second .unit) (fun _ => ret (1, .pair .unit .unit))) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SwitchingDoublingExample.two_leg_exit

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.SwitchingExample
