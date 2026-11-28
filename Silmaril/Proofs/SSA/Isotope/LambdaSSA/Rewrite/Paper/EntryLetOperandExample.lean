module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Example.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Substitution.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.Erasure.Thms
public import Silmaril.Semantics.Calco2019.Maybe.Types.Thms

/-! # Repair a cyclic square with a state-forgetting constructor -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetOperandExample

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift)
open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory
open Paper.WithEntryLet (Site repairTarget uniformity_of_target_move ofRegion_comp_constructor)
open Paper.WithEntryLet.OperandExample Paper.EntryLetObstruction
open Paper.Extension.Singleton (projection projectStep iterateChosen projectSquare_iff)
open SequencingObstruction (Instruction)

local notation "J" => projection Seed

set_option backward.isDefEq.respectTransparency false

private theorem left_forget : (sumCofan (Φ := Instruction) U U).inl ≫ forget = discardArrow U := by
  rw [sumCofan_inl]
  exact discard_comp_branchValue (.inl (.var rfl))

private theorem right_forget : (sumCofan (Φ := Instruction) U U).inr ≫ forget = discardArrow U := by
  rw [sumCofan_inr]
  exact discard_comp_branchValue (.inr (.var rfl))

private theorem recurringTarget_eq {r : Region Instruction} (hr : ValueBranches [U] r [U]) :
    ofRegion (CfgEta.TypeCategory.seqValueBranches hr
      (s := .br 0 (.inr .unit)) (.br rfl (.inr .unit))) ≫ (sumIso U U).hom =
      ofRegion hr ≫ discardArrow U ≫ coprod.inr := by
  let h : ValueBranches [U] (.br 0 (.inr .unit) : Region Instruction) [Bit] :=
    .br rfl (.inr .unit)
  have leg : discardArrow (Φ := Instruction) U ≫ (sumCofan U U).inr = ofRegion h := by
    rw [sumCofan_inr]
    rfl
  rw [← ofRegion_comp hr h (CfgEta.TypeCategory.seqValueBranches hr h), ← leg]
  simp

theorem movedTarget_eq :
    ofRegion movedStep_typed ≫ (sumIso U U).hom =
      ofRegion movedRequest_typed ≫ discardArrow U ≫ coprod.inr :=
  recurringTarget_eq movedRequest_typed

theorem flatTarget_eq :
    ofRegion flatStep_typed ≫ (sumIso U U).hom =
      ofRegion flatRequest_typed ≫ discardArrow U ≫ coprod.inr :=
  recurringTarget_eq flatRequest_typed

theorem taggedSource_forget (q : X ⟶ X) :
    taggedSource q ≫ coprod.map (𝟙 X) forget = forget ≫ q ≫ discardArrow U ≫ coprod.inr := by
  let i : X ⟶ D := (sumCofan U U).inl
  let j : X ⟶ D := (sumCofan U U).inr
  let d : X ⟶ X := discardArrow U
  let e := sumIso (Φ := Instruction) U U
  let arm (k : X ⟶ D) : X ⟶ X ⨿ D := d ≫ q ≫ d ≫ k ≫ coprod.inr
  have repeat_arm (k : X ⟶ D) (hk : k ≫ forget = d) :
      arm k ≫ coprod.map (𝟙 X) forget = d ≫ q ≫ d ≫ coprod.inr := by
    have discard_idem : d ≫ d = d := discard_comp_branchValue .unit
    simp only [arm, Category.assoc, coprod.inr_map]
    rw [← Category.assoc k forget, hk, ← Category.assoc d d, discard_idem]
  have eliminate : e.inv ≫ forget = coprod.desc d d := by
    have hl : coprod.inl ≫ e.inv = i := by
      rw [← sumCofan_inl_sumIso_hom U U, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have hr : coprod.inr ≫ e.inv = j := by
      rw [← sumCofan_inr_sumIso_hom U U, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    apply coprod.hom_ext
    · rw [← Category.assoc, hl, coprod.inl_desc, left_forget]
    · rw [← Category.assoc, hr, coprod.inr_desc, right_forget]
  apply (cancel_epi e.inv).1
  change e.inv ≫ (e.hom ≫ coprod.desc (arm i) (arm j)) ≫ coprod.map (𝟙 X) forget =
    e.inv ≫ forget ≫ q ≫ d ≫ coprod.inr
  rw [Category.assoc e.hom, Iso.inv_hom_id_assoc, ← Category.assoc e.inv forget, eliminate]
  apply coprod.hom_ext
  · rw [← Category.assoc, coprod.inl_desc, repeat_arm i left_forget, coprod.inl_desc_assoc]
  · rw [← Category.assoc, coprod.inr_desc, repeat_arm j right_forget, coprod.inr_desc_assoc]

private theorem repaired_square :
    source ≫ coprod.map (𝟙 X) forget = forget ≫ ofRegion movedStep_typed ≫ (sumIso U U).hom := by
  rw [movedTarget_eq]
  exact taggedSource_forget _

private theorem move_written : Site.here.move flatRecurringRequest = some movedRecurringRequest := by
  simp only [flatRecurringRequest, flatRequest, movedRecurringRequest, movedRequest, compLSubst, lsubst, Site.move, Site.rewriteAt, Site.moveEntry]
  congr 2
  apply congrArg (Region.cfg (.br 0 (.var 0) : Region Instruction) 2)
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun j => j.elim0)) i

private abbrev substForget : Nat → Tm Instruction := Tm.singleSubst .unit ∘ lift Nat.succ

private theorem substForget_typed :
    ∀ ⦃i A⦄, At [U] i A → Tm.BranchValue [Bit] (substForget i) A := by
  intro i A hi
  cases i with
  | zero => cases Option.some.inj hi; exact .unit
  | succ i => simp [At] at hi

private theorem movedComposite :
    ValueBranches [Bit] (movedRecurringRequest.substVars substForget) [Bit] :=
  movedStep_typed.substVars substForget_typed

private theorem move_composite :
    Site.here.move (flatRecurringRequest.substVars substForget) = some (movedRecurringRequest.substVars substForget) := by
  rw [Site.move_substVars, move_written]
  rfl

private theorem native_composite :
    source ≫ coprod.map (𝟙 X) forget = ofRegion movedComposite ≫ (sumIso U U).hom := by
  have ex : forget ≫ ofRegion movedStep_typed = ofRegion movedComposite :=
    ofRegion_comp_constructor (.unit (Γ := [Bit])) movedStep_typed movedComposite
  rw [repaired_square, ← Category.assoc forget, ex]

theorem native_square_ne :
    source ≫ coprod.map (𝟙 X) forget ≠ forget ≫ target := by
  have flatComposite : ValueBranches [Bit] (flatRecurringRequest.substVars substForget) [Bit] :=
    flatStep_typed.substVars substForget_typed
  have ex : forget ≫ ofRegion flatStep_typed = ofRegion flatComposite :=
    ofRegion_comp_constructor (.unit (Γ := [Bit])) flatStep_typed flatComposite
  intro comm
  rw [native_composite, target, ← Category.assoc forget, ex] at comm
  have eq := (ofRegion_eq_iff movedComposite flatComposite).1
    ((cancel_mono (sumIso U U).hom).1 comm)
  exact discardedRecurringRequest_ne eq

theorem repaired :
    ∃ g : X ⟶ X ⨿ X, projectStep Seed g = projectStep Seed target ∧
      source ≫ coprod.map (𝟙 X) forget = forget ≫ g :=
  repairTarget .here (.unit (Γ := [Bit])) flatStep_typed source movedComposite move_composite native_composite

theorem corrected_square :
    projectStep Seed source ≫ coprod.map (𝟙 ((J).obj X)) ((J).map forget) =
      (J).map forget ≫ projectStep Seed target := by
  obtain ⟨g, hg, native⟩ := repaired
  rw [← hg]
  exact (projectSquare_iff Seed source g forget).2 (congrArg ((J).map) native)

theorem corrected_iterate :
    iterateChosen Seed (projectStep Seed source) =
      (J).map forget ≫ iterateChosen Seed (projectStep Seed target) :=
  uniformity_of_target_move .here (.unit (Γ := [Bit])) flatStep_typed source
    movedComposite move_composite native_composite

section DistinctTags

open scoped MonoidalCategory
open Semantics.Interaction.Typed (AtomValues typeModel)
open Semantics.Categorical
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)

local instance : AtomValues Empty where
  carrier a := a.elim

attribute [local instance] typeModel

local instance : HasEff Instruction Bool where
  eff _ := false

local notation "Maybe" => Silmaril.Calco2019.Maybe.Types.Model
local notation "M" => ofMonadicTypeModel (τ := Ty Empty)
local notation "K" => typeJ (m := Maybe)

local instance : InstructionModel Instruction (Ty Empty) Bool Maybe where
  denote _ x := pure x
  denotePure _ _ x := x
  denote_pure _ _ _ := rfl

local instance : Silmaril.Isotope.LetIter.Semantics.Categorical.InstructionModel K M Instruction :=
  ofMonadicInstructionModel (ε := Bool)

private theorem projected_tags_ne :
    (J).map (sumCofan (Φ := Instruction) U U).inl ≠ (J).map (sumCofan U U).inr := by
  let : RegionTypingCoherent (Φ := Instruction) K M :=
    Semantics.Erasure.regionTypingCoherent (κ := Empty) (Φ := Instruction) (m := Maybe)
      (fun _ x => pure x) (.inr .unit) (.inr .unit)
      (fun f x => by cases f; cases x; rfl)
  intro eq
  let F := Paper.WithEntryLet.denoteFunctor (Φ := Instruction) K M (fun _ _ => ⟨rfl, rfl⟩)
  have e := congrArg (fun k => F.map k) eq
  dsimp only [F] at e
  rw [sumCofan_inl, sumCofan_inr, Paper.WithEntryLet.denoteFunctor_map_ofRegion,
    Paper.WithEntryLet.denoteFunctor_map_ofRegion,
    denoteSingletonRegion_br K M (.inl (.var (i := 0) rfl)),
    denoteSingletonRegion_br K M (.inr (.var (i := 0) rfl))] at e
  simp only [lookup, ← Functor.map_comp] at e
  change (K).map (coprod.inl ≫ (Types.binaryCoproductIso PUnit PUnit).hom) =
    (K).map (coprod.inr ≫ (Types.binaryCoproductIso PUnit PUnit).hom) at e
  rw [Types.binaryCoproductIso_inl_comp_hom, Types.binaryCoproductIso_inr_comp_hom] at e
  have out := congrArg (fun k => k.of PUnit.unit) e
  change Sum.inl (Sum.inl PUnit.unit) = Sum.inl (Sum.inr PUnit.unit) at out
  have tags : (Sum.inl PUnit.unit : PUnit ⊕ PUnit) = .inr PUnit.unit := Sum.inl.inj out
  cases tags

theorem no_retraction : ¬ ∃ k : (J).obj X ⟶ (J).obj D, (J).map forget ≫ k = 𝟙 ((J).obj D) := by
  rintro ⟨k, hk⟩
  let i : X ⟶ D := (sumCofan U U).inl
  let j : X ⟶ D := (sumCofan U U).inr
  have eq : (J).map i = (J).map j := by
    calc
      _ = ((J).map i ≫ (J).map forget) ≫ k := by rw [Category.assoc, hk, Category.comp_id]
      _ = ((J).map j ≫ (J).map forget) ≫ k := by
        rw [← Functor.map_comp, ← Functor.map_comp, left_forget, right_forget]
      _ = _ := by rw [Category.assoc, hk, Category.comp_id]
  exact projected_tags_ne eq

end DistinctTags

theorem move_recurring_request : Site.here.move flatRecurringRequest = some movedRecurringRequest :=
  move_written

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetOperandExample
