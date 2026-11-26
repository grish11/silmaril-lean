module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Square.Example.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.CartesianBoundary.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Substitution.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SequencingObstruction.SquareReplay

/-! # A native square from a forward script and a certified inverse -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.SquareReplayExample

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open WithBoundEntryEta.SquareReplay.Example
open WithBoundEntryEta.CaseReplay
open WithBoundEntryEta.ScriptReplay
open WithEntryLet.OperandExample (Bit D X forget)
open EntryLetObstruction (U discardInput)
open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory
open Extension.Singleton (projectStep projection projectSquare_iff iterateChosen uniformity_of_constructor_square)

local notation "J" => projection Seed

set_option backward.isDefEq.respectTransparency false

private theorem trace : Trace [U] [U] [.unaryEntry .here] work movedWork :=
  .cons workTyped.hasType rfl (.nil movedWorkTyped.hasType)

private theorem shared : CommonTableAt [U] [Bit] site hoisted := by
  have rows : ValueBranches [U] (.let₁ tick (.cfg entry 2 flatRows)) [Bit] := flatTyped
  cases rows with
  | let₁ ha hcfg =>
    cases hcfg with
    | cfg R he hb =>
      cases he with
      | case hdisc hl hr =>
        exact .unaryBody ha (.here R hdisc hl.hasType hr.hasType (fun i => (hb i).hasType))

private theorem specializeValues :
    ∀ ⦃i A⦄, At [U] i A → Tm.BranchValue [Bit] (discardInput i) A := by
  intro i A hi
  cases i with
  | zero => cases Option.some.inj hi; exact .unit
  | succ i => simp [At] at hi

private theorem beforeHoist : hoistAt site flat = some hoisted := rfl

private theorem inverseStep : hoistAt site (flat.substVars discardInput) = some (hoisted.substVars discardInput) := by
  rw [hoistAt_substVars, beforeHoist]
  rfl

private theorem guardedPredecessor (q) (h : hoistAt site q = some hoisted) :
    ValueBranches [U] q [Bit] :=
  (hoistAt_injective site beforeHoist h) ▸ flatTyped

private theorem recurring_eq {r : Region SequencingObstruction.Instruction}
    (hw : ValueBranches [U] r [U]) :
    ofRegion (CfgEta.TypeCategory.seqValueBranches hw repeatTyped) ≫ (sumIso U U).hom =
      ofRegion hw ≫ discardArrow U ≫ coprod.inr := by
  have leg : discardArrow U ≫ (sumCofan U U).inr = ofRegion repeatTyped := by
    rw [sumCofan_inr]
    rfl
  rw [← ofRegion_comp hw repeatTyped (CfgEta.TypeCategory.seqValueBranches hw repeatTyped), ← leg]
  simp

private theorem post_forget : post ≫ coprod.map (𝟙 X) forget = discardArrow U ≫ coprod.inr := by
  have leftForget : (sumCofan U U).inl ≫ forget = discardArrow U := by
    rw [sumCofan_inl]
    exact discard_comp_branchValue (.inl (.var rfl))
  let discard : X ⟶ X := discardArrow U
  have idem : discard ≫ discard = discard := discard_comp_branchValue .unit
  unfold post
  simp only [Category.assoc, coprod.inr_map]
  rw [← Category.assoc (sumCofan U U).inl, leftForget, ← Category.assoc (discardArrow U)]
  exact congrArg (fun k => k ≫ coprod.inr) idem

private theorem source_post {r : Region SequencingObstruction.Instruction}
    (hw : ValueBranches [U] r [U]) :
    (forget ≫ ofRegion hw ≫ post) ≫ coprod.map (𝟙 X) forget =
      forget ≫ (ofRegion (CfgEta.TypeCategory.seqValueBranches hw repeatTyped) ≫ (sumIso U U).hom) := by
  rw [recurring_eq hw]
  simp only [Category.assoc, post_forget]

theorem native_square_ne : source ≫ coprod.map (𝟙 X) forget ≠ forget ≫ target := by
  let left := writtenFlatTyped.substVars specializeValues
  let right := hoistedTyped.substVars specializeValues
  have hleft : forget ≫ ofRegion writtenFlatTyped = ofRegion left :=
    WithEntryLet.ofRegion_comp_constructor .unit writtenFlatTyped left
  have hright : forget ≫ ofRegion hoistedTyped = ofRegion right :=
    WithEntryLet.ofRegion_comp_constructor .unit hoistedTyped right
  have sourceEq : source ≫ coprod.map (𝟙 X) forget =
      forget ≫ (ofRegion writtenFlatTyped ≫ (sumIso U U).hom) :=
    source_post workTyped
  intro h
  rw [sourceEq, target, ← Category.assoc forget, ← Category.assoc forget, hleft, hright] at h
  exact Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Sequencing.squareReplay_ne
    ((ofRegion_eq_iff left right).1 ((cancel_mono (sumIso U U).hom).1 h))

theorem repaired :
    ∃ g : X ⟶ X ⨿ X,
      projectStep Seed movedSource = projectStep Seed source ∧ projectStep Seed g = projectStep Seed target ∧
      movedSource ≫ coprod.map (𝟙 X) forget = forget ≫ g := by
  let specialized := flatTyped.substVars specializeValues
  have hsub : forget ≫ ofRegion flatTyped = ofRegion specialized :=
    WithEntryLet.ofRegion_comp_constructor .unit flatTyped specialized
  have native : movedSource ≫ coprod.map (𝟙 X) forget = ofRegion specialized ≫ (sumIso U U).hom := by
    change (forget ≫ ofRegion movedWorkTyped ≫ post) ≫ _ = _
    rw [source_post movedWorkTyped]
    change forget ≫ (ofRegion flatTyped ≫ (sumIso U U).hom) = _
    rw [← Category.assoc, hsub]
  exact WithBoundEntryEta.SquareReplay.repair workTyped movedWorkTyped trace forget post
    .unit hoistedTyped site shared inverseStep guardedPredecessor specialized native

theorem corrected_square :
    projectStep Seed source ≫ coprod.map (𝟙 ((J).obj X)) ((J).map forget) =
      (J).map forget ≫ projectStep Seed target := by
  obtain ⟨g, hs, ht, native⟩ := repaired
  rw [← hs, ← ht]
  exact (projectSquare_iff Seed movedSource g forget).2 (congrArg (J).map native)

theorem corrected_iterate :
    iterateChosen Seed (projectStep Seed source) =
      (J).map forget ≫ iterateChosen Seed (projectStep Seed target) := by
  obtain ⟨g, hs, ht, native⟩ := repaired
  rw [← hs, ← ht]
  exact uniformity_of_constructor_square Seed ⟨.unit, .unit, rfl⟩ movedSource g native

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.SquareReplayExample
