module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Doubling.Switching.Example.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SwitchingDoublingExample

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.TypeCategory Paper.TypeCategory.SwitchingExample
open CategoryTheory CategoryTheory.Limits
open Silmaril.Elgot.ITree
open Semantics.Interaction
open Silmaril.Isotope.LambdaSSA.Semantics (extend)

local notation "E" => Event Op Empty

set_option backward.isDefEq.respectTransparency false

private theorem left_step : stateLeft ≫ step = left ≫ coprod.map (𝟙 AnswerObj) stateRight :=
  inl_blockCopair _ _

private theorem right_step : stateRight ≫ step = right ≫ coprod.map (𝟙 AnswerObj) stateLeft :=
  inr_blockCopair _ _

private theorem right_exit : flagLeft ≫ right = ofRegion secondExitTyped ≫ coprod.inl := by
  unfold right
  rw [← Category.assoc flagLeft,
    show flagLeft ≫ (sumIso U U).hom = coprod.inl from sumCofan_inl_sumIso_hom _ _,
    coprod.inl_desc]

private theorem left_twice :
    left ≫ coprod.desc coprod.inl right = ofRegion outcomeTyped ≫
      (coprod.inl : AnswerObj ⟶ AnswerObj ⨿ FlagObj) := by
  have requests : ofRegion (requestTyped .first) ≫ ofRegion secondExitTyped = ofRegion twoRequestsTyped :=
    ofRegion_comp (requestTyped .first) secondExitTyped twoRequestsTyped
  have outcomeEq : (sumIso U U).hom ≫
      coprod.desc (ofRegion earlyTyped) (ofRegion twoRequestsTyped) = ofRegion outcomeTyped :=
    coprod_desc_ofRegion earlyTyped twoRequestsTyped
  unfold left
  rw [Category.assoc, coprod.desc_comp]
  simp only [Category.assoc, coprod.inl_desc, coprod.inr_desc, right_exit]
  rw [← Category.assoc (ofRegion (requestTyped .first)) (ofRegion secondExitTyped), requests]
  rw [← coprod.desc_comp, ← Category.assoc, outcomeEq]


theorem ordered_typed : ValueBranches [Flag] orderedOutcome [U, PairTy] := by
  apply outcomeTyped.lsubst
  intro i C hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    exact .case (.var rfl) (.br (ℓ := 0) rfl (.var rfl)) (.br (ℓ := 1) rfl (.var rfl))
  | succ i => simp [At] at hi

theorem actual_left : stateLeft ≫ doubled = ofRegion outcomeTyped ≫ coprod.inl := by
  have restriction : stateLeft ≫ doubled =
      (left ≫ coprod.desc coprod.inl right) ≫ coprod.map (𝟙 AnswerObj) stateLeft :=
    (switching_double_rows (X := Flag) (Y := Flag) (B := Answer) step left right left_step right_step).1
  rw [restriction, left_twice, Category.assoc, coprod.inl_map, Category.id_comp]

theorem right_repeat : flagRight ≫ right = ofRegion (requestTyped .second) ≫ flagRight ≫ coprod.inr := by
  unfold right
  rw [← Category.assoc flagRight,
    show flagRight ≫ (sumIso U U).hom = coprod.inr from sumCofan_inr_sumIso_hom _ _,
    coprod.inr_desc]

theorem iterates_agree : iterate doubled = iterate step :=   iterate_double_of_switching_rows_with_exit step left right left_step right_step

theorem left_iterates :
    stateLeft ≫ iterate doubled = ofRegion outcomeTyped ∧
    stateLeft ≫ iterate step = ofRegion outcomeTyped := by
  have done : stateLeft ≫ iterate doubled = ofRegion outcomeTyped := by
    rw [iterate_fixpoint doubled, ← Category.assoc stateLeft, actual_left, Category.assoc,
      coprod.inl_desc, Category.comp_id]
  exact ⟨done, iterates_agree ▸ done⟩

private theorem ordered_syntax :
    orderedOutcome =
      .case (.var 0)
        (.case (.inl (.var 0)) (.br 0 (.var 0)) (.br 1 (.var 0)))
        (SwitchingExample.request .first (SwitchingExample.request .second
          (.case (.inr (.pair .unit .unit)) (.br 0 (.var 0)) (.br 1 (.var 0))))) := rfl

theorem immediate_exit :
    region (F := E) Semantics.Interaction.request (fun _ => .inl .unit) orderedOutcome =
      ret (0, .unit) := by
  rw [ordered_syntax]
  simp only [region, term, pure_bind, extend]
  rfl

theorem two_leg_exit :
    region (F := E) Semantics.Interaction.request (fun _ => .inr .unit) orderedOutcome =
      vis (.call .first .unit) (fun _ =>
        vis (.call .second .unit) (fun _ => ret (1, .pair .unit .unit))) := by
  rw [ordered_syntax]
  simp only [SwitchingExample.request, region, term,
    Semantics.Interaction.request, pure_bind, vis_bind, extend]
  rfl

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SwitchingDoublingExample
