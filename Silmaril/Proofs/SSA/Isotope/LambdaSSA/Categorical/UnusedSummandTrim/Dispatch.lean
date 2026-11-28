module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.Readback.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandTrim.Rows
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandFamily
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandTyping
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Live.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Labels.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Case.Thms

/-! # Restrict actual contextual iteration to the written jump targets -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandTrim

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.UnusedSummand
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandTyping
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (fst snd)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel case_inl_context)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext contextualLoop)

variable {κ : Type u} {Φ : Type v} [HasTy Φ (Ty κ)]
variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty κ) V) [InstructionModel J M Φ]

set_option backward.isDefEq.respectTransparency false in
omit [InstructionModel J M Φ] in
theorem residual_ext {n : Nat} (R : Fin n → Ty κ) (written : Fin n → Prop)
    (Γ : VCtx (Ty κ)) (nonempty : Nonempty (Subtype written))
    {X : C} {f g : J.obj (ctxObj M Γ ⊗ Residual M R written) ⟶ X}
    (agree : ∀ i, J.map (ctxObj M Γ ◁ targetInject M written R i) ≫ f =
      J.map (ctxObj M Γ ◁ targetInject M written R i) ≫ g) : f = g := by
  classical
  let _ := Fintype.ofFinite (Subtype written)
  let _ := nonempty
  obtain ⟨m, card⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := Subtype written))
  let e : Fin (m + 1) ≃ Subtype written :=
    (finCongr card.symm).trans (Fintype.equivFin (Subtype written)).symm
  let iso := Sigma.reindex e (fun i : Subtype written => M.obj (R i.val))
  have inj (i : Fin (m + 1)) :
      finiteLabelInject M (fun j => R (e j).val) i ≫ iso.hom = targetInject M written R (e i) :=
    Sigma.ι_reindex_hom e (fun j : Subtype written => M.obj (R j.val)) i
  have eq : J.map (ctxObj M Γ ◁ iso.hom) ≫ f = J.map (ctxObj M Γ ◁ iso.hom) ≫ g := by
    apply collective_ext J M m Γ (fun j => R (e j).val)
    intro i
    simp only [MonoidalCategory.id_tensorHom, ← J.map_comp_assoc,
      ← MonoidalCategory.whiskerLeft_comp, inj]
    exact agree (e i)
  have := congrArg (fun h => J.map (ctxObj M Γ ◁ iso.inv) ≫ h) eq
  simpa only [← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id,
    MonoidalCategory.whiskerLeft_id, J.map_id, Category.id_comp] using this

variable {k : Nat} {R S : Fin (k + 1) → Ty κ} {L : LCtx (Ty κ)} {Γ : VCtx (Ty κ)}
  (p : Program (Φ := Φ) R L Γ)

local notation "Env" => ctxObj M Γ
local notation "Result" => labelObj M L
local notation "Target" => Subtype p.targets
local notation "Local" => Residual M R p.targets

private noncomputable abbrev entryResidual : J.obj Env ⟶ J.obj (Result ⨿ Local) :=
  evalResidual M p.targets J p.entry (fun _ h => .inl h)

private noncomputable abbrev rowResidual (i : Fin (k + 1)) : J.obj Env ⟶ J.obj (Result ⨿ Local) :=
  evalResidual M p.targets J (p.blocks i) (fun _ h => .inr ⟨i, h⟩)

set_option backward.isDefEq.respectTransparency false in
private theorem from_exact (roll : IterationRolling C) (tag : Bool)
    {f : J.obj Env ⟶ J.obj Result}
    (w : CfgDenotesAt J M S (p.entry.region tag id)
      (fun i => (p.blocks i).region tag Nat.succ) f) :
    ∃ reduced : J.obj (Env ⊗ Local) ⟶ J.obj (Result ⨿ Local),
      (∀ i : Target, J.map (Env ◁ targetInject M p.targets R i) ≫ reduced =
        J.map (fst Env (M.obj (R i.val))) ≫ rowResidual J M p i.val) ∧
      f = caseWithContext J (entryResidual J M p) (J.map (snd Env Result)) (contextualLoop J reduced) := by
  obtain ⟨he, hb, e, bs, large, entry, blocks, rows, rfl⟩ := w
  obtain ⟨tails, tag_eq, shape⟩ :=
    Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandFamily.targets_from_typing p tag he hb
  subst tag
  let inc := includeTargets M p.targets tails shape
  let cut := labelAppendSplit M (List.ofFn S) L
  obtain ⟨mid, mid_rows⟩ := collective_exists J M k Γ S (Result ⨿ Local)
    (fun i => J.map (fst Env (M.obj (S i))) ≫ rowResidual J M p i)
  let middle := J.map (Env ◁ labelObjToFinite M S) ≫ mid
  let reduced := J.map (Env ◁ inc) ≫ middle
  have entry_eq : e ≫ J.map cut =
      entryResidual J M p ≫ J.map (coprod.map (𝟙 Result) inc) := by
    have eq := row_into_residual M p.targets J (Ren.id Γ) (𝟙 Env) (fun _ _ _ => Category.id_comp _)
      tails shape p.entry (fun _ h => .inl h) entry
    simpa only [J.map_id, Category.id_comp] using eq
  have rows_eq : large ≫ J.map cut = mid ≫ J.map (coprod.map (𝟙 Result) inc) := by
    apply collective_ext J M k Γ S
    intro i
    erw [← Category.assoc _ large, rows.restrict i, ← Category.assoc _ mid, mid_rows i, Category.assoc]
    exact row_into_residual M p.targets J (Ren.wk Γ (S i)) (fst Env (M.obj (S i)))
      (fun _ _ _ => rfl) tails shape (p.blocks i) (fun _ h => .inr ⟨i, h⟩) (blocks i)
  refine ⟨reduced, ?_, ?_⟩
  · intro i
    have route : targetInject M p.targets R i ≫ inc ≫ labelObjToFinite M S =
        selectedPayload M p.targets tails shape i ≫ finiteLabelInject M S i.val := by
      erw [includeTargets_inject_assoc M p.targets tails shape i,
        labelObjToFinite_local M S i.val (local_label S i.val)]
    unfold reduced middle
    rw [← J.map_comp_assoc, ← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalCategory.whiskerLeft_comp, Category.assoc, route, MonoidalCategory.whiskerLeft_comp,
      J.map_comp_assoc]
    have selected := mid_rows i.val
    rw [MonoidalCategory.id_tensorHom] at selected
    rw [selected, ← J.map_comp_assoc, CartesianMonoidalCategory.whiskerLeft_fst]
  · have computed := cfgDispatch_of_state_factorization J roll inc (entryResidual J M p) middle
    unfold middle at computed
    rw [Category.assoc] at computed
    unfold cfgDispatchArrow
    rw [MonoidalCategory.id_tensorHom, entry_eq, ← Category.assoc _ large, Category.assoc, rows_eq]
    exact computed.symm

set_option backward.isDefEq.respectTransparency false in
theorem compare_trimmed (roll : IterationRolling C) {tag tag' : Bool}
    {t : (p.region tag).HasType Γ L} {t' : (p.region tag').HasType Γ L}
    {f g : J.obj Env ⟶ J.obj Result} (d : RegionDenotes J M t f) (e : RegionDenotes J M t' g) : f = g := by
  obtain ⟨_, left⟩ := d.cfg_readback J M
  obtain ⟨_, right⟩ := e.cfg_readback J M
  obtain ⟨step, step_rows, eq⟩ := from_exact J M p roll tag left
  obtain ⟨step', step_rows', eq'⟩ := from_exact J M p roll tag' right
  rw [eq, eq']
  cases isEmpty_or_nonempty Target with
  | inl empty =>
      obtain ⟨out, entry⟩ := residual_exits M p.targets J empty p.entry (fun _ h => .inl h)
      unfold entryResidual
      rw [entry, case_inl_context, case_inl_context]
  | inr nonempty =>
      rw [residual_ext J M R p.targets Γ nonempty (fun i => (step_rows i).trans (step_rows' i).symm)]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandTrim
