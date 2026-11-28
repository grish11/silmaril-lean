module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.BlockParameters.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandBlockParameters.Typing
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandTyping
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandTrim.Rows
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandTrim.Dispatch
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Live.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Labels.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Case.Thms

/-! # Trim an actual CFG graph after recovering its parameter types -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandBlockParameters

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.UnusedSummand.BlockParameters
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandTyping (local_label)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandTrim
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

variable {k : Nat} {R S : Fin (k + 1) → Ty κ} {L : LCtx (Ty κ)} {Γ : VCtx (Ty κ)}
  (p : Program (Φ := Φ) R L Γ)

local notation "Env" => ctxObj M Γ
local notation "Result" => labelObj M L
local notation "Target" => Subtype p.targets
local notation "Local" => Residual M R p.targets
local notation "LabelCtx" => List.ofFn S ++ L

private noncomputable abbrev entryResidual : J.obj Env ⟶ J.obj (Result ⨿ Local) :=
  evalResidual M p.targets J p.entry (fun _ h => .inl h)

private noncomputable def blockResidual {i : Fin (k + 1)} (block : Block (Φ := Φ) R L Γ i)
    (hits : ∀ j, block.targets j → p.targets j) :
    J.obj (ctxObj M (R i :: Γ)) ⟶ J.obj (Result ⨿ Local) :=
  match block with
  | .parameter row => evalResidual M p.targets J row hits
  | .captured row => J.map (fst Env (M.obj (R i))) ≫ evalResidual M p.targets J row hits

set_option backward.isDefEq.respectTransparency false in
private theorem block_factors {i : Fin (k + 1)} (block : Block (Φ := Φ) R L Γ i)
    (hits : ∀ j, block.targets j → p.targets j) (shape : ∀ j, p.targets j → S j = R j)
    {B : Ty κ} (parameter : block.hasParameter → B = R i)
    {hb : block.region.HasType (B :: Γ) LabelCtx}
    {f : J.obj (ctxObj M (B :: Γ)) ⟶ J.obj (labelObj M LabelCtx)}
    (w : RegionDenotes J M hb f) :
    ∃ mid : J.obj (ctxObj M (B :: Γ)) ⟶ J.obj (Result ⨿ Local),
      f ≫ J.map (labelAppendSplit M (List.ofFn S) L) =
        mid ≫ J.map (coprod.map (𝟙 Result) (includeTargets M p.targets none shape)) ∧
      ∀ eq : B = R i, J.map (Env ◁ eqToHom (congrArg M.obj eq.symm)) ≫ mid =
        blockResidual J M p block hits := by
  cases block with
  | parameter row =>
      obtain rfl := parameter True.intro
      refine ⟨evalResidual M p.targets J row hits, ?_, ?_⟩
      · have eq := row_into_residual M p.targets J (Ren.id (R i :: Γ)) (𝟙 _)
          (fun _ _ _ => Category.id_comp _) none shape row hits w
        simpa only [J.map_id, Category.id_comp] using eq
      · intro _
        simp only [eqToHom_refl, MonoidalCategory.whiskerLeft_id, J.map_id, Category.id_comp]
        rfl
  | captured row =>
      refine ⟨J.map (fst Env (M.obj B)) ≫ evalResidual M p.targets J row hits, ?_, ?_⟩
      · simpa only [Category.assoc] using row_into_residual M p.targets J (Ren.wk Γ B)
          (fst Env (M.obj B)) (fun _ _ _ => rfl) none shape row hits w
      · intro eq
        subst B
        simp only [eqToHom_refl, MonoidalCategory.whiskerLeft_id, J.map_id, Category.id_comp]
        rfl

theorem readback_reached {t : p.region.HasType Γ L} {f : J.obj Env ⟶ J.obj Result}
    (d : RegionDenotes J M t f) :
    ∃ S : Fin (k + 1) → Ty κ,
      CfgDenotesAt J M S (p.entry.region false id) (fun i => (p.blocks i).region) f ∧
      ∀ i, p.Reaches i → S i = R i := by
  obtain ⟨S, selected⟩ := d.cfg_readback J M
  refine ⟨S, selected, ?_⟩
  obtain ⟨he, hb, _, _, _, _, _, _, _⟩ := selected
  exact fun _ path => type_at_reached p he hb path

set_option backward.isDefEq.respectTransparency false in
private theorem from_exact (roll : IterationRolling C) (closed : p.ReachableParameters)
    {f : J.obj Env ⟶ J.obj Result}
    (w : CfgDenotesAt J M S (p.entry.region false id) (fun i => (p.blocks i).region) f)
    (aligned : ∀ i, p.Reaches i → S i = R i) :
    ∃ reduced : J.obj (Env ⊗ Local) ⟶ J.obj (Result ⨿ Local),
      (∀ i : Target, J.map (Env ◁ targetInject M p.targets R i) ≫ reduced =
        blockResidual J M p (p.blocks i.val) (fun _ h => .inr ⟨i.val, h⟩)) ∧
      f = caseWithContext J (entryResidual J M p) (J.map (snd Env Result)) (contextualLoop J reduced) := by
  obtain ⟨_, _, e, bs, large, entry, blocks, rows, rfl⟩ := w
  have shape (i : Fin (k + 1)) (hit : p.targets i) : S i = R i :=
    aligned i (closed.targets i hit)
  let inc := includeTargets M p.targets none shape
  let cut := labelAppendSplit M (List.ofFn S) L
  choose mid factor restricted using fun i =>
    block_factors J M p (p.blocks i) (fun _ h => .inr ⟨i, h⟩) shape
      (fun h => aligned i (closed.parameters i h)) (blocks i)
  obtain ⟨joint, joint_rows⟩ := collective_exists J M k Γ S (Result ⨿ Local) mid
  let middle := J.map (Env ◁ labelObjToFinite M S) ≫ joint
  let reduced := J.map (Env ◁ inc) ≫ middle
  have entry_eq : e ≫ J.map cut = entryResidual J M p ≫ J.map (coprod.map (𝟙 Result) inc) := by
    have eq := row_into_residual M p.targets J (Ren.id Γ) (𝟙 Env) (fun _ _ _ => Category.id_comp _)
      none shape p.entry (fun _ h => .inl h) entry
    simpa only [J.map_id, Category.id_comp] using eq
  have rows_eq : large ≫ J.map cut = joint ≫ J.map (coprod.map (𝟙 Result) inc) := by
    apply collective_ext J M k Γ S
    intro i
    erw [← Category.assoc _ large, rows.restrict i, ← Category.assoc _ joint, joint_rows i]
    exact factor i
  refine ⟨reduced, ?_, ?_⟩
  · intro i
    have route : targetInject M p.targets R i ≫ inc ≫ labelObjToFinite M S =
        selectedPayload M p.targets none shape i ≫ finiteLabelInject M S i.val := by
      erw [includeTargets_inject_assoc M p.targets none shape i,
        labelObjToFinite_local M S i.val (local_label S i.val)]
    unfold reduced middle
    rw [← J.map_comp_assoc, ← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalCategory.whiskerLeft_comp, Category.assoc, route, MonoidalCategory.whiskerLeft_comp,
      J.map_comp_assoc]
    have selected := joint_rows i.val
    rw [MonoidalCategory.id_tensorHom] at selected
    rw [selected, selectedPayload_none]
    exact restricted i.val (shape i.val i.property)
  · have computed := cfgDispatch_of_state_factorization J roll inc (entryResidual J M p) middle
    unfold middle at computed
    rw [Category.assoc] at computed
    unfold cfgDispatchArrow
    rw [MonoidalCategory.id_tensorHom, entry_eq, ← Category.assoc _ large, Category.assoc, rows_eq]
    exact computed.symm

set_option backward.isDefEq.respectTransparency false in
theorem compare (roll : IterationRolling C) (closed : p.ReachableParameters)
    {t : p.region.HasType Γ L} {f g : J.obj Env ⟶ J.obj Result}
    (d : RegionDenotes J M t f) (e : RegionDenotes J M t g) : f = g := by
  obtain ⟨_, left, leftTypes⟩ := readback_reached J M p d
  obtain ⟨_, right, rightTypes⟩ := readback_reached J M p e
  obtain ⟨step, step_rows, eq⟩ := from_exact J M p roll closed left leftTypes
  obtain ⟨step', step_rows', eq'⟩ := from_exact J M p roll closed right rightTypes
  rw [eq, eq']
  cases isEmpty_or_nonempty Target with
  | inl empty =>
      obtain ⟨out, entry⟩ := residual_exits M p.targets J empty p.entry (fun _ h => .inl h)
      unfold entryResidual
      rw [entry, case_inl_context, case_inl_context]
  | inr nonempty =>
      rw [residual_ext J M R p.targets Γ nonempty (fun i => (step_rows i).trans (step_rows' i).symm)]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandBlockParameters
