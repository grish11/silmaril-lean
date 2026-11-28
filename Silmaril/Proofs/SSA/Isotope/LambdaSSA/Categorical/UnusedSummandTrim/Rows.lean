module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.Readback.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummand
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandTyping
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Labels.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.Renaming.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.Renaming.Product.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Case.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Naturality.Thms

/-! # Read row transfers into the coproduct of written targets -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandTrim

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.UnusedSummand
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandTyping
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandProof (payloadChange payloadChange_none payloadChange_some bind_transfer)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical
  (TypeModel InstructionModel case_pre_map case_postcomp)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (bind caseWithContext)

variable {κ : Type u} {Φ : Type v} [HasTy Φ (Ty κ)]
variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (M : TypeModel (Ty κ) V) {n : Nat} {R S : Fin n → Ty κ} (written : Fin n → Prop)

noncomputable abbrev Residual (R : Fin n → Ty κ) (written : Fin n → Prop) : V :=
  ∐ fun i : Subtype written => M.obj (R i.val)

noncomputable abbrev targetInject (R : Fin n → Ty κ) (i : Subtype written) :
    M.obj (R i.val) ⟶ Residual M R written :=
  Sigma.ι (fun j : Subtype written => M.obj (R j.val)) i

noncomputable def selectedPayload (tails : Option (Fin n → Ty κ))
    (shape : ∀ i, written i → S i = family R tails i) (i : Subtype written) :
    M.obj (R i.val) ⟶ M.obj (S i.val) :=
  payloadChange M R tails i.val ≫ eqToHom (congrArg M.obj (shape i.val i.property).symm)

set_option backward.isDefEq.respectTransparency false in
theorem selectedPayload_none (shape : ∀ i, written i → S i = R i) (i : Subtype written) :
    selectedPayload M written none shape i = eqToHom (congrArg M.obj (shape i.val i.property).symm) := by
  simp only [selectedPayload, payloadChange_none, Category.id_comp]

noncomputable def includeTargets (tails : Option (Fin n → Ty κ))
    (shape : ∀ i, written i → S i = family R tails i) :
    Residual M R written ⟶ labelObj M (List.ofFn S) :=
  Sigma.desc fun i => selectedPayload M written tails shape i ≫
    labelInject M (L := List.ofFn S) i.val (by simp [At])

@[reassoc] theorem includeTargets_inject (tails : Option (Fin n → Ty κ))
    (shape : ∀ i, written i → S i = family R tails i) (i : Subtype written) :
    targetInject M written R i ≫ includeTargets M written tails shape =
      selectedPayload M written tails shape i ≫ labelInject M (L := List.ofFn S) i.val (by simp [At]) :=
  Sigma.ι_comp_desc _ _

-- Transport the exact selected payload type while retaining the numeric label.
private theorem castLookup {L : LCtx (Ty κ)} {i : Nat} {A B : Ty κ}
    (eq : A = B) (h : At L i B) : At L i A :=
  eq ▸ h

private theorem inject_cast {L : LCtx (Ty κ)} {i : Nat} {A B : Ty κ}
    (eq : A = B) (h : At L i B) :
    labelInject M i (castLookup eq h) = eqToHom (congrArg M.obj eq) ≫ labelInject M i h := by
  subst B
  simp

variable {C : Type u₂} [Category.{v₂} C]
  [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J] [InstructionModel J M Φ]
  {L : LCtx (Ty κ)}

noncomputable def evalResidual {Γ : VCtx (Ty κ)} (r : Row (Φ := Φ) R L Γ)
    (hits : ∀ i, r.targets i → written i) :
    J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L ⨿ Residual M R written) :=
  match r with
  | .jump i a => denote J M (operand_base a) ≫
      J.map (targetInject M written R ⟨i, hits i rfl⟩ ≫ coprod.inr)
  | .let₁ value body =>
      bind J (denote J M (operand_base value)) (evalResidual body hits)
  | .let₂ value body =>
      bindProduct J M (denote J M (operand_base value)) (evalResidual body hits)
  | .exit i h a => denote J M (operand_base a) ≫ J.map (labelInject M i h ≫ coprod.inl)
  | .case a l r => caseWithContext J
      (denote J M (operand_base a) ≫ J.map (M.coprodIso _ _).hom)
      (evalResidual l (fun i h => hits i (.inl h)))
      (evalResidual r (fun i h => hits i (.inr h)))

set_option backward.isDefEq.respectTransparency false in
omit [SymmetricCategory V] [DistributiveTensor V] in
private theorem localRoute (tails : Option (Fin n → Ty κ))
    (shape : ∀ i, written i → S i = family R tails i) (i : Subtype written) :
    labelInject M i.val (castLookup (shape i.val i.property).symm (local_append S L i.val)) ≫
      labelAppendSplit M (List.ofFn S) L =
    eqToHom (congrArg M.obj (shape i.val i.property).symm) ≫
      labelInject M i.val (local_label S i.val) ≫ coprod.inr := by
  rw [inject_cast M (shape i.val i.property).symm (local_append S L i.val), Category.assoc]
  erw [labelAppendSplit_local M S L i.val (local_append S L i.val) (local_label S i.val)]

set_option backward.isDefEq.respectTransparency false in
private theorem row_build {Γ Δ : VCtx (Ty κ)} {ρ : Nat → Nat} (ren : Ren Γ Δ ρ)
    (p : ctxObj M Δ ⟶ ctxObj M Γ)
    (reads : ∀ ⦃i A⦄ (h : At Γ i A), p ≫ lookup M i h = lookup M (ρ i) (ren h))
    (tails : Option (Fin n → Ty κ)) (shape : ∀ i, written i → S i = family R tails i)
    (r : Row (Φ := Φ) R L Γ) (hits : ∀ i, r.targets i → written i) :
    ∃ (t : (r.region tails.isSome ρ).HasType Δ (List.ofFn S ++ L)) (f : _),
      DeterminedRegion Δ (r.region tails.isSome ρ) (List.ofFn S ++ L) ∧
      RegionDenotes J M t f ∧
      f ≫ J.map (labelAppendSplit M (List.ofFn S) L) =
        J.map p ≫ evalResidual M written J r hits ≫
          J.map (coprod.map (𝟙 (labelObj M L)) (includeTargets M written tails shape)) := by
  induction r generalizing Δ ρ with
  | jump i a =>
      let j : Subtype written := ⟨i, hits i rfl⟩
      let target := castLookup (shape i j.property).symm (local_append S L i)
      have da := (denote_spec J M (operand_base a)).rename J M ren reads
      cases tails with
      | none =>
          refine ⟨_, _, .br target (operand_determined ren a), RegionDenotes.br (h := target) da, ?_⟩
          simp only [evalResidual, Category.assoc, ← J.map_comp, coprod.inr_map]
          rw [localRoute M written none shape j, includeTargets_inject_assoc M written none shape j]
          simp [selectedPayload, payloadChange_none]
      | some D =>
          refine ⟨_, _, .br target (.inl (operand_determined ren a)),
            RegionDenotes.br (h := target) (Denotes.inl (B := D i) da), ?_⟩
          simp only [evalResidual, Category.assoc, ← J.map_comp, coprod.inr_map]
          rw [localRoute M written (some D) shape j,
            includeTargets_inject_assoc M written (some D) shape j]
          simp [selectedPayload, payloadChange_some, Category.assoc, j]
  | exit i h a =>
      have da := (denote_spec J M (operand_base a)).rename J M ren reads
      refine ⟨_, _, .br (exit_append S h) (operand_determined ren a),
        RegionDenotes.br (h := exit_append S h) da, ?_⟩
      simp only [evalResidual, Category.assoc, ← J.map_comp, coprod.inl_map, Category.id_comp]
      erw [labelAppendSplit_exit M S L h (exit_append S h)]
  | @let₁ Γ A value body ih =>
      have dv := (denote_spec J M (operand_base value)).rename J M ren reads
      obtain ⟨_, _, determined, db, body_eq⟩ :=
        ih (ren.lift A) (p ▷ M.obj A) (lookup_liftRename M ren reads A) hits
      refine ⟨_, _, .let₁ (operand_type ren value) (operand_determined ren value) determined,
        RegionDenotes.let₁ dv db, ?_⟩
      simpa only [evalResidual] using bind_transfer J p (denote J M (operand_base value)) body_eq
  | @let₂ Γ A B value body ih =>
      have dv := (denote_spec J M (operand_base value)).rename J M ren reads
      obtain ⟨_, _, determined, db, body_eq⟩ :=
        ih ((ren.lift A).lift B) ((p ▷ M.obj A) ▷ M.obj B)
          (lookup_liftRename M (ren.lift A) (lookup_liftRename M ren reads A) B) hits
      refine ⟨_, _, .let₂ (operand_type ren value) (operand_determined ren value) determined,
        RegionDenotes.let₂ dv db, ?_⟩
      simpa only [evalResidual, bindProduct, ctxObj] using bindProduct_transfer J M p (denote J M (operand_base value)) body_eq
  | @case Γ A B a l r ihl ihr =>
      have da := (denote_spec J M (operand_base a)).rename J M ren reads
      obtain ⟨_, _, ld, dl, left⟩ := ihl (ren.lift A) (p ▷ M.obj A)
        (lookup_liftRename M ren reads A) (fun i h => hits i (.inl h))
      obtain ⟨_, _, rd, dr, right⟩ := ihr (ren.lift B) (p ▷ M.obj B)
        (lookup_liftRename M ren reads B) (fun i h => hits i (.inr h))
      refine ⟨_, _, .case (operand_type ren a) (operand_determined ren a) ld rd,
        RegionDenotes.case da dl dr, ?_⟩
      simp only [evalResidual, case_postcomp, left, right, Category.assoc]
      rw [case_pre_map]

theorem row_into_residual {Γ Δ : VCtx (Ty κ)} {ρ : Nat → Nat} (ren : Ren Γ Δ ρ)
    (p : ctxObj M Δ ⟶ ctxObj M Γ)
    (reads : ∀ ⦃i A⦄ (h : At Γ i A), p ≫ lookup M i h = lookup M (ρ i) (ren h))
    (tails : Option (Fin n → Ty κ)) (shape : ∀ i, written i → S i = family R tails i)
    (r : Row (Φ := Φ) R L Γ) (hits : ∀ i, r.targets i → written i)
    {t : (r.region tails.isSome ρ).HasType Δ (List.ofFn S ++ L)}
    {f : J.obj (ctxObj M Δ) ⟶ J.obj (labelObj M (List.ofFn S ++ L))}
    (w : RegionDenotes J M t f) :
    f ≫ J.map (labelAppendSplit M (List.ofFn S) L) =
      J.map p ≫ evalResidual M written J r hits ≫
        J.map (coprod.map (𝟙 (labelObj M L)) (includeTargets M written tails shape)) := by
  obtain ⟨_, _, determined, d, eq⟩ := row_build M written J ren p reads tails shape r hits
  rw [determined.denotes_eq J M w d, eq]

set_option backward.isDefEq.respectTransparency false in
theorem residual_exits (notarget : IsEmpty (Subtype written))
    {Δ : VCtx (Ty κ)} (r : Row (Φ := Φ) R L Δ) (hits : ∀ i, r.targets i → written i) :
    ∃ out : J.obj (ctxObj M Δ) ⟶ J.obj (labelObj M L),
      evalResidual M written J r hits =
        out ≫ J.map (coprod.inl : labelObj M L ⟶ labelObj M L ⨿ Residual M R written) := by
  induction r with
  | jump i _ => exact (notarget.false ⟨i, hits i rfl⟩).elim
  | exit i h a =>
      exact ⟨denote J M (operand_base a) ≫ J.map (labelInject M i h), by
        simp only [evalResidual, Category.assoc, J.map_comp]⟩
  | let₁ value body ih =>
      obtain ⟨out, eq⟩ := ih hits
      exact ⟨bind J (denote J M (operand_base value)) out, by
        simp only [evalResidual, eq, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, Category.assoc]⟩
  | let₂ value body ih =>
      obtain ⟨out, eq⟩ := ih hits
      exact ⟨bindProduct J M (denote J M (operand_base value)) out, by
        simp only [evalResidual, eq, bindProduct_postcomp]⟩
  | case arg left right ihl ihr =>
      obtain ⟨outl, eql⟩ := ihl (fun i h => hits i (.inl h))
      obtain ⟨outr, eqr⟩ := ihr (fun i h => hits i (.inr h))
      refine ⟨caseWithContext J (denote J M (operand_base arg) ≫ J.map (M.coprodIso _ _).hom)
        outl outr, ?_⟩
      erw [case_postcomp]
      simp only [evalResidual, eql, eqr]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandTrim
