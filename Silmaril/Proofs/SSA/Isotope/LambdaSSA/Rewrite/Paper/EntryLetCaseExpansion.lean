module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.CaseExpansion.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Example.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Initial.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Endpoint.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Substitution.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.CaseRepair.Thms

/-! # A native duplication step obstructs repair of just the target -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetCaseExpansion

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift)
open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory
open Paper.WithEntryLet (Site ofRegion_comp_constructor projectSquare_of_native_move)
open Paper.WithEntryLet.OperandExample hiding source corrected_square corrected_iterate
open Paper.WithEntryLet.CaseExpansion Paper.EntryLetObstruction
open Paper.Extension.Singleton (projection projectStep iterateChosen)
open Paper.Extension.Singleton.CaseRepair (restore restore_post_iff repairSource)
open SequencingObstruction (Instruction)

local notation "J" => projection Seed

set_option backward.isDefEq.respectTransparency false

private theorem discard_values (Γ : VCtx (Ty Empty)) :
    ∀ ⦃i A⦄, At [U] i A → Tm.BranchValue Γ (discardInput i) A := by
  intro i A hi
  cases i with
  | zero => cases Option.some.inj hi; exact .unit
  | succ i => simp [At] at hi

private theorem discard_typed {r : Region Instruction} (hr : ValueBranches [U] r [Bit])
    (Γ : VCtx (Ty Empty)) : ValueBranches Γ (r.substVars discardInput) [Bit] :=
  hr.substVars (discard_values Γ)

private theorem rename_discarded {r : Region Instruction} (hr : ValueBranches [U] r [Bit])
    (ρ : Nat → Nat) : (r.substVars discardInput).renameVars ρ = r.substVars discardInput := by
  rw [renameVars_substVars]
  exact Paper.SingletonReification.SingleCfg.singleton_subst hr.hasType rfl

private theorem duplicated_typed : ValueBranches [Bit] duplicatedRequest [Bit] :=
  .case (.var rfl) ((discard_typed flatStep_typed [Bit]).renameVars (Ren.wk [Bit] U))
    ((discard_typed flatStep_typed [Bit]).renameVars (Ren.wk [Bit] U))

theorem native_expansion : Paper.Eqv [Bit] (flatRecurringRequest.substVars discardInput) duplicatedRequest [Bit] :=
  (Paper.case_ignoring (A := U) (B := U) (i := 0) rfl (discard_typed flatStep_typed [Bit]).hasType).symm

theorem move_one_copy : (Site.leftArm .here).move duplicatedRequest = some oneMovedRequest := by
  have hm : Site.here.move (flatRecurringRequest.substVars discardInput) =
      some (movedRecurringRequest.substVars discardInput) := by
    rw [Site.move_substVars, move_recurring_request]
    rfl
  change (Site.here.move ((flatRecurringRequest.substVars discardInput).renameVars Nat.succ)).map
    (fun r => Region.case (.var 0) r ((flatRecurringRequest.substVars discardInput).renameVars Nat.succ)) =
      some (Region.case (.var 0) ((movedRecurringRequest.substVars discardInput).renameVars Nat.succ)
        ((flatRecurringRequest.substVars discardInput).renameVars Nat.succ))
  rw [renameVars_eq_substVars, Site.move_substVars, hm]
  simp only [Option.map_some, renameVars_eq_substVars]

theorem oneMovedRequest_typed : ValueBranches [Bit] oneMovedRequest [Bit] :=
  (Site.move_sound (.leftArm .here) duplicated_typed move_one_copy).1

private theorem left_forget : (sumCofan (Φ := Instruction) U U).inl ≫ forget = discardArrow U := by
  rw [sumCofan_inl]
  exact discard_comp_branchValue (.inl (.var rfl))

private theorem right_forget : (sumCofan (Φ := Instruction) U U).inr ≫ forget = discardArrow U := by
  rw [sumCofan_inr]
  exact discard_comp_branchValue (.inr (.var rfl))

private theorem source_arms :
    source ≫ coprod.map (𝟙 X) forget =
      (sumIso U U).hom ≫ coprod.desc
        (discardArrow U ≫ ofRegion movedRequest_typed ≫ discardArrow U ≫ coprod.inr)
        (discardArrow U ≫ ofRegion flatRequest_typed ≫ discardArrow U ≫ coprod.inr) := by
  rw [source, Category.assoc, coprod.desc_comp]
  simp only [Category.assoc, taggedSource_forget]
  rw [← Category.assoc (sumCofan (Φ := Instruction) U U).inl forget, left_forget,
    ← Category.assoc (sumCofan (Φ := Instruction) U U).inr forget, right_forget]

theorem source_composite :
    source ≫ coprod.map (𝟙 X) forget = ofRegion oneMovedRequest_typed ≫ (sumIso U U).hom := by
  have hl := ofRegion_comp_constructor (.unit (Γ := [U])) movedStep_typed (discard_typed movedStep_typed [U])
  have hr := ofRegion_comp_constructor (.unit (Γ := [U])) flatStep_typed (discard_typed flatStep_typed [U])
  change discardArrow U ≫ _ = _ at hl hr
  rw [source_arms, ← movedTarget_eq, ← flatTarget_eq, ← Category.assoc (discardArrow U),
    ← Category.assoc (discardArrow U), hl, hr, ← coprod.desc_comp, ← Category.assoc,
    coprod_desc_ofRegion]
  congr 1
  apply (ofRegion_eq_iff _ oneMovedRequest_typed).2
  change Paper.Eqv [Bit] (.case (.var 0) ((movedRecurringRequest.substVars discardInput).renameVars
    (lift Nat.succ)) ((flatRecurringRequest.substVars discardInput).renameVars (lift Nat.succ)))
    oneMovedRequest [Bit]
  simp only [oneMovedRequest, rename_discarded movedStep_typed, rename_discarded flatStep_typed]
  exact .refl (ValueBranches.case (.var (i := 0) (rfl : At [Bit] 0 Bit))
    (discard_typed movedStep_typed [U, Bit]) (discard_typed flatStep_typed [U, Bit])).hasType

theorem no_target_repair (g : X ⟶ X ⨿ X) :
    source ≫ coprod.map (𝟙 X) forget ≠ forget ≫ g := by
  obtain ⟨r, hr, e⟩ := exists_ofRegion (g ≫ (sumIso U U).inv)
  have hg : g = ofRegion hr ≫ (sumIso U U).hom := by
    rw [← e, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have he : forget ≫ ofRegion hr = ofRegion (discard_typed hr [Bit]) :=
    ofRegion_comp_constructor (.unit (Γ := [Bit])) hr (discard_typed hr [Bit])
  intro hs
  rw [source_composite, hg, ← Category.assoc forget, he] at hs
  exact oneMovedRequest_no_image r ((ofRegion_eq_iff _ oneMovedRequest_typed).1
    ((cancel_mono (sumIso U U).hom).1 hs.symm))

theorem corrected_square :
    projectStep Seed source ≫ coprod.map (𝟙 ((J).obj X)) ((J).map forget) =
      (J).map forget ≫ projectStep Seed target := by
  have he : forget ≫ ofRegion flatStep_typed = ofRegion (discard_typed flatStep_typed [Bit]) :=
    ofRegion_comp_constructor (.unit (Γ := [Bit])) flatStep_typed (discard_typed flatStep_typed [Bit])
  apply projectSquare_of_native_move (.leftArm .here) source target forget
    (discard_typed flatStep_typed [Bit]) duplicated_typed native_expansion move_one_copy source_composite
  rw [target, ← Category.assoc forget, he]

theorem source_repaired :
    ∃ f : D ⟶ X ⨿ D, projectStep Seed f = projectStep Seed source ∧
      f ≫ coprod.map (𝟙 X) forget = forget ≫ target := by
  let split := (sumIso (Φ := Instruction) U U).symm
  let l : X ⟶ D := (sumCofan U U).inl
  let r : X ⟶ D := (sumCofan U U).inr
  let d : X ⟶ X := discardArrow U
  have left_tag : coprod.inl ≫ split.hom = l := by
    change (coprod.inl : X ⟶ X ⨿ X) ≫ (sumIso U U).inv = l
    rw [← sumCofan_inl_sumIso_hom U U, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have right_tag : coprod.inr ≫ split.hom = r := by
    change (coprod.inr : X ⟶ X ⨿ X) ≫ (sumIso U U).inv = r
    rw [← sumCofan_inr_sumIso_hom U U, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have left_hom : l ≫ (sumIso U U).hom = (coprod.inl : X ⟶ X ⨿ X) :=
    sumCofan_inl_sumIso_hom U U
  have right_hom : r ≫ (sumIso U U).hom = (coprod.inr : X ⟶ X ⨿ X) :=
    sumCofan_inr_sumIso_hom U U
  have tagged (q : X ⟶ X) :
      taggedSource q = (sumIso U U).hom ≫
        coprod.desc (d ≫ q ≫ d ≫ l ≫ (coprod.inr : D ⟶ X ⨿ D))
          (d ≫ q ≫ d ≫ r ≫ (coprod.inr : D ⟶ X ⨿ D)) := rfl
  have left_source (q : X ⟶ X) :
      l ≫ taggedSource q = d ≫ q ≫ d ≫ l ≫ coprod.inr := by
    rw [tagged, ← Category.assoc l, left_hom, coprod.inl_desc]
  have right_source (q : X ⟶ X) :
      r ≫ taggedSource q = d ≫ q ≫ d ≫ r ≫ coprod.inr := by
    rw [tagged, ← Category.assoc r, right_hom, coprod.inr_desc]
  let p : X ⟶ X ⨿ X := d ≫ ofRegion movedRequest_typed ≫ d ≫ coprod.inr
  let q : X ⟶ X ⨿ X := d ≫ ofRegion flatRequest_typed ≫ d ≫ coprod.inr
  have recover : source = restore split l r (source ≫ coprod.map (𝟙 X) forget) := by
    rw [source_arms]
    unfold source restore
    apply congrArg ((sumIso U U).hom ≫ ·)
    apply congrArg₂ coprod.desc
    · rw [left_source, ← Category.assoc coprod.inl split.hom, left_tag]
      change _ = l ≫ ((sumIso U U).hom ≫ coprod.desc p q) ≫ coprod.map (𝟙 X) l
      rw [Category.assoc (sumIso U U).hom, ← Category.assoc l (sumIso U U).hom,
        left_hom, coprod.inl_desc_assoc]
      simp only [p, Category.assoc, coprod.inr_map]
    · rw [right_source, ← Category.assoc coprod.inr split.hom, right_tag]
      change _ = r ≫ ((sumIso U U).hom ≫ coprod.desc p q) ≫ coprod.map (𝟙 X) r
      rw [Category.assoc (sumIso U U).hom, ← Category.assoc r (sumIso U U).hom,
        right_hom, coprod.inr_desc_assoc]
      simp only [q, Category.assoc, coprod.inr_map]
  have keep (s : X ⟶ D) (eq : s ≫ forget = d) :
      (forget ≫ target) ≫ coprod.map (𝟙 X) (s ≫ forget) = forget ≫ target := by
    have idem : d ≫ d = d := discard_comp_branchValue .unit
    rw [eq, target, flatTarget_eq]
    simp only [Category.assoc, coprod.inr_map]
    rw [← Category.assoc d d, idem]
    rfl
  have image : restore split l r (forget ≫ target) ≫ coprod.map (𝟙 X) forget = forget ≫ target :=
    (restore_post_iff split l r forget _).2
      ⟨congrArg (coprod.inl ≫ split.hom ≫ ·) (keep l left_forget),
       congrArg (coprod.inr ≫ split.hom ≫ ·) (keep r right_forget)⟩
  exact ⟨_, repairSource Seed split l r forget source target corrected_square (congrArg ((J).map) recover) image⟩

theorem corrected_iterate :
    iterateChosen Seed (projectStep Seed source) =
      (J).map forget ≫ iterateChosen Seed (projectStep Seed target) := by
  obtain ⟨f, hf, native⟩ := source_repaired
  rw [← hf]
  exact Paper.Extension.Singleton.uniformity_of_constructor_square Seed ⟨.unit, .unit, rfl⟩ f target native

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetCaseExpansion
