module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Square.Example.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.CartesianBoundary.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Substitution.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SequencingObstruction.SquareReplay

/-! # A native square from a forward script and a certified inverse -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.SquareReplayExample

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open WithBoundEntryEta.SquareReplay.Example
open WithBoundEntryEta.CaseReplay
open WithBoundEntryEta.ScriptReplay
open WithBoundEntryEta.NativeFrame (linear_composite split_composite repeating_guarded specialize_guarded)
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

private theorem beforeHoist : hoistAt site flat = some hoisted := rfl

private theorem inverseStep : hoistAt site (flat.substVars discardInput) = some (hoisted.substVars discardInput) := by
  rw [hoistAt_substVars, beforeHoist]
  rfl

private theorem guardedPredecessor (q) (h : hoistAt site q = some hoisted) :
    ValueBranches [U] q [Bit] :=
  (hoistAt_injective site beforeHoist h) ▸ flatTyped

private theorem leftForget : (sumCofan U U).inl ≫ forget = discardArrow U := by
  rw [sumCofan_inl]
  exact discard_comp_branchValue (.inl (.var rfl))

private theorem rightForget : (sumCofan U U).inr ≫ forget = discardArrow U := by
  rw [sumCofan_inr]
  exact discard_comp_branchValue (.inr (.var rfl))

private theorem source_endpoint {r : Region SequencingObstruction.Instruction}
    (hw : ValueBranches [U] r [U]) :
    (forget ≫ ofRegion hw ≫ post) ≫ coprod.map (𝟙 X) forget =
      ofRegion (specialize_guarded (.unit (Γ := [Bit]))
        (repeating_guarded (B := U) hw (.unit (Γ := [U])))) ≫ (sumIso U U).hom := by
  let discard : X ⟶ X := discardArrow U
  let next : X ⟶ D := discard ≫ (sumCofan U U).inl
  have idem : discard ≫ discard = discard := discard_comp_branchValue .unit
  have route : next ≫ forget = discard := by
    change (discard ≫ (sumCofan U U).inl) ≫ forget = discard
    rw [Category.assoc, leftForget, idem]
  have endpoint := linear_composite (B := U) hw (.unit (Γ := [Bit])) (.unit (Γ := [U])) next route
  calc
    (forget ≫ ofRegion hw ≫ post) ≫ coprod.map (𝟙 X) forget =
        (forget ≫ ofRegion hw ≫ next ≫ coprod.inr) ≫ coprod.map (𝟙 X) forget := by
      simp only [next, discard, post, Category.assoc]
      rfl
    _ = _ := endpoint

theorem native_square_ne : source ≫ coprod.map (𝟙 X) forget ≠ forget ≫ target := by
  let left := specialize_guarded (.unit (Γ := [Bit])) writtenFlatTyped
  let right := specialize_guarded (.unit (Γ := [Bit])) hoistedTyped
  have hright : forget ≫ ofRegion hoistedTyped = ofRegion right :=
    WithEntryLet.ofRegion_comp_constructor .unit hoistedTyped right
  have sourceEq : source ≫ coprod.map (𝟙 X) forget =
      ofRegion left ≫ (sumIso U U).hom :=
    source_endpoint workTyped
  intro h
  rw [sourceEq, target, ← Category.assoc forget, hright] at h
  exact Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Sequencing.squareReplay_ne
    ((ofRegion_eq_iff left right).1 ((cancel_mono (sumIso U U).hom).1 h))

theorem repaired :
    ∃ g : X ⟶ X ⨿ X,
      projectStep Seed movedSource = projectStep Seed source ∧ projectStep Seed g = projectStep Seed target ∧
      movedSource ≫ coprod.map (𝟙 X) forget = forget ≫ g := by
  let specialized := specialize_guarded (.unit (Γ := [Bit])) flatTyped
  have native : movedSource ≫ coprod.map (𝟙 X) forget = ofRegion specialized ≫ (sumIso U U).hom :=
    source_endpoint movedWorkTyped
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

theorem alternating_routes (round : X ⟶ X) :
    (sumCofan U U).inl ≫ alternating round =
      (sumCofan U U).inl ≫ forget ≫ round ≫ (sumCofan U U).inr ≫ coprod.inr ∧
    (sumCofan U U).inr ≫ alternating round =
      (sumCofan U U).inr ≫ forget ≫ round ≫ (sumCofan U U).inl ≫ coprod.inr := by
  constructor <;> simp [alternating, WithBoundEntryEta.NativeFrame.split, ← Category.assoc] <;> rfl

theorem alternating_native_square :
    alternating (ofRegion movedWorkTyped) ≫ coprod.map (𝟙 X) forget =
      forget ≫ (ofRegion flatTyped ≫ (sumIso U U).hom) := by
  let specialized := specialize_guarded (.unit (Γ := [Bit])) flatTyped
  have hsub : forget ≫ ofRegion flatTyped = ofRegion specialized :=
    WithEntryLet.ofRegion_comp_constructor .unit flatTyped specialized
  rw [← Category.assoc forget, hsub]
  exact split_composite (B := U) (X := U) (Y := U) movedWorkTyped
    (.unit (Γ := [Bit])) (.unit (Γ := [U])) (sumCofan U U).inr (sumCofan U U).inl rightForget leftForget

private theorem alternating_projected_source :
    projectStep Seed (alternating (ofRegion movedWorkTyped)) =
      projectStep Seed (alternating (ofRegion workTyped)) := by
  have eq := (Extension.Singleton.ofRegion_eq_iff Seed movedWorkTyped workTyped).2 trace.eqv.symm
  let l : X ⟶ D := (sumCofan U U).inl
  let r : X ⟶ D := (sumCofan U U).inr
  have arm (incoming next : X ⟶ D) :
      (J).map (incoming ≫ forget ≫ ofRegion movedWorkTyped ≫ next ≫ (coprod.inr : D ⟶ X ⨿ D)) =
      (J).map (incoming ≫ forget ≫ ofRegion workTyped ≫ next ≫ (coprod.inr : D ⟶ X ⨿ D)) := by
    simp only [Functor.map_comp, eq]
  let output : Paper.TypeCategory (τ := Ty Empty) SequencingObstruction.Instruction := X ⨿ D
  have desc := Extension.Singleton.projection_map_desc_congr Seed
    (A := U) (B := U) (C := output) (arm l r) (arm r l)
  unfold projectStep alternating WithBoundEntryEta.NativeFrame.split
  simp only [Functor.map_comp]
  rw [desc]

theorem alternating_corrected_iterate :
    iterateChosen Seed (projectStep Seed (alternating (ofRegion workTyped))) =
      (J).map forget ≫ iterateChosen Seed (projectStep Seed target) := by
  let flatStep : X ⟶ X ⨿ X := ofRegion flatTyped ≫ (sumIso U U).hom
  have sameTarget : projectStep Seed flatStep = projectStep Seed target := by
    have eq := (Extension.Singleton.ofRegion_eq_iff Seed flatTyped hoistedTyped).2
      (hoistAt_guarded site flatTyped beforeHoist).2
    unfold projectStep flatStep target
    simp only [Functor.map_comp, eq]
  rw [← alternating_projected_source, ← sameTarget]
  exact uniformity_of_constructor_square Seed ⟨.unit, .unit, rfl⟩
    (alternating (ofRegion movedWorkTyped)) flatStep alternating_native_square

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.SquareReplayExample
