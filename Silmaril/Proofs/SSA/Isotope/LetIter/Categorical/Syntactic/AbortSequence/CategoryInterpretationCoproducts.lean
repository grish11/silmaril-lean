module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Interpretation.Coproducts.Defs

/-! # Preservation of coproducts by the repaired computation interpretation -/

public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.InterpretationCoproductProofs

universe u u₁ u₂ v₁ v₂

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Thesis.LambdaIter.Syn (SynCat)
open Silmaril.Thesis.LambdaIter.Syn.SynCat (cop copIso injl injr)

open Silmaril.Thesis.LambdaIter.Syn.SynCat (injl_copIso_hom injr_copIso_hom)
open Silmaril.Thesis.LambdaIter.LocallyNameless (HasType)
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] (pe : ε)
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V) [InstructionModel J M Φ]

local notation "modelSig" => signature (τ := τ) (Φ := Φ) pe
local notation "P" => repairedProjection (τ := τ) (Φ := Φ) pe
local notation "Q" => RepairedSynCat (τ := τ) (Φ := Φ) pe

variable
  (coherent : TypingCoherent (ν := Empty) J M Φ)
  (shared : ∀ R T : V, ∃ e : J.obj R ⊗ J.obj T = J.obj (R ⊗ T),
    Functor.StrongPremonoidal.tensorIso (J := J) R T = eqToIso e)
  (pureInstr : ∀ f : Φ, IsPure pe f → ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
    InstructionModel.denote (J := J) (M := M) f = J.map p)

local notation "F" => repairedComputationFunctor pe J M coherent shared pureInstr

theorem syntaxInl (X Y : Q) :
    (P).map (injl X.as Y.as) ≫ (repairedSyntaxCoprodIso pe X Y).hom = coprod.inl := by
  change (P).map (injl X.as Y.as) ≫ (P).map (copIso X.as Y.as).hom ≫
    (repairedProjectionCoprodIso pe X.as Y.as).hom = _
  rw [← (P).map_comp_assoc, injl_copIso_hom, repairedProjection_coprodIso_inl pe]
  rfl

theorem syntaxInr (X Y : Q) :
    (P).map (injr X.as Y.as) ≫ (repairedSyntaxCoprodIso pe X Y).hom = coprod.inr := by
  change (P).map (injr X.as Y.as) ≫ (P).map (copIso X.as Y.as).hom ≫
    (repairedProjectionCoprodIso pe X.as Y.as).hom = _
  rw [← (P).map_comp_assoc, injr_copIso_hom, repairedProjection_coprodIso_inr pe]
  rfl


local instance : Thesis.LambdaIter.TypeFormers τ := Bridge.thesisTypeFormers τ
local instance : Thesis.LambdaIter.HasTy Φ τ := Bridge.thesisHasTy Φ τ
local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

include coherent shared pureInstr in
private theorem normalizeNewest (X : SynCat modelSig) :
    J.map (singletonEnvIso M X.ty).inv ≫
      denote J M (Derivation.bv (Φ := Φ) (Γ := Γ₀) (β := .snoc .nil X.ty) (ι := 0)) =
      𝟙 (J.obj (M.obj X.ty)) := by
  have h := repairedArrowDenote_mk pe J M coherent shared pureInstr (X := X) (Y := X)
    HasType.newest (.bv (ι := 0))
  change (F).map ((P).map (𝟙 X)) = _ at h
  exact h.symm.trans (((P) ⋙ (F)).map_id X)

include coherent shared pureInstr in
private theorem mapSyntaxInl (X Y : Q) :
    (F).map ((P).map (injl X.as Y.as)) =
      J.map (coprod.inl ≫ (M.coprodIso X.as.ty Y.as.ty).inv) := by
  have h := repairedArrowDenote_mk pe J M coherent shared pureInstr
    (X := X.as) (Y := cop X.as Y.as) (HasType.inl HasType.newest) (Derivation.inl .bv)
  change (F).map ((P).map (injl X.as Y.as)) = _ at h
  rw [h]
  change J.map (singletonEnvIso M X.as.ty).inv ≫
    denote J M (Derivation.bv (Φ := Φ) (Γ := Γ₀) (β := .snoc .nil X.as.ty) (ι := 0)) ≫
    J.map (coprod.inl ≫ (M.coprodIso X.as.ty Y.as.ty).inv) = _
  rw [← Category.assoc, normalizeNewest pe J M coherent shared pureInstr X.as]
  exact Category.id_comp (J.map (coprod.inl ≫ (M.coprodIso X.as.ty Y.as.ty).inv))

include coherent shared pureInstr in
private theorem mapSyntaxInr (X Y : Q) :
    (F).map ((P).map (injr X.as Y.as)) =
      J.map (coprod.inr ≫ (M.coprodIso X.as.ty Y.as.ty).inv) := by
  have h := repairedArrowDenote_mk pe J M coherent shared pureInstr
    (X := Y.as) (Y := cop X.as Y.as) (HasType.inr HasType.newest) (Derivation.inr .bv)
  change (F).map ((P).map (injr X.as Y.as)) = _ at h
  rw [h]
  change J.map (singletonEnvIso M Y.as.ty).inv ≫
    denote J M (Derivation.bv (Φ := Φ) (Γ := Γ₀) (β := .snoc .nil Y.as.ty) (ι := 0)) ≫
    J.map (coprod.inr ≫ (M.coprodIso X.as.ty Y.as.ty).inv) = _
  rw [← Category.assoc, normalizeNewest pe J M coherent shared pureInstr Y.as]
  exact Category.id_comp (J.map (coprod.inr ≫ (M.coprodIso X.as.ty Y.as.ty).inv))

theorem mapInl (X Y : Q) :
    (F).map (coprod.inl : X ⟶ X ⨿ Y) ≫
      (repairedComputationCoprodIso pe J M coherent shared pureInstr X Y).hom = coprod.inl := by
  let κ := repairedSyntaxCoprodIso pe X Y
  have source : (coprod.inl : X ⟶ X ⨿ Y) ≫ κ.inv = (P).map (injl X.as Y.as) := by
    have h : (P).map (injl X.as Y.as) ≫ κ.hom = (coprod.inl : _ ⟶ X ⨿ Y) :=
      syntaxInl pe X Y
    rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change (F).map coprod.inl ≫ (F).map κ.inv ≫ J.map (M.coprodIso X.as.ty Y.as.ty).hom ≫
    inv (coprodComparison J (M.obj X.as.ty) (M.obj Y.as.ty)) = _
  rw [← (F).map_comp_assoc, source, mapSyntaxInl]
  have target : J.map (coprod.inl ≫ (M.coprodIso X.as.ty Y.as.ty).inv) ≫
      J.map (M.coprodIso X.as.ty Y.as.ty).hom ≫
      inv (coprodComparison J (M.obj X.as.ty) (M.obj Y.as.ty)) = coprod.inl := by
    rw [← J.map_comp_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      ← inl_coprodComparison, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  exact target

theorem mapInr (X Y : Q) :
    (F).map (coprod.inr : Y ⟶ X ⨿ Y) ≫
      (repairedComputationCoprodIso pe J M coherent shared pureInstr X Y).hom = coprod.inr := by
  let κ := repairedSyntaxCoprodIso pe X Y
  have source : (coprod.inr : Y ⟶ X ⨿ Y) ≫ κ.inv = (P).map (injr X.as Y.as) := by
    have h : (P).map (injr X.as Y.as) ≫ κ.hom = (coprod.inr : _ ⟶ X ⨿ Y) :=
      syntaxInr pe X Y
    rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change (F).map coprod.inr ≫ (F).map κ.inv ≫ J.map (M.coprodIso X.as.ty Y.as.ty).hom ≫
    inv (coprodComparison J (M.obj X.as.ty) (M.obj Y.as.ty)) = _
  rw [← (F).map_comp_assoc, source, mapSyntaxInr]
  have target : J.map (coprod.inr ≫ (M.coprodIso X.as.ty Y.as.ty).inv) ≫
      J.map (M.coprodIso X.as.ty Y.as.ty).hom ≫
      inv (coprodComparison J (M.obj X.as.ty) (M.obj Y.as.ty)) = coprod.inr := by
    rw [← J.map_comp_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      ← inr_coprodComparison, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  exact target

theorem comparison (X Y : Q) : coprodComparison (F) X Y =
    (repairedComputationCoprodIso pe J M coherent shared pureInstr X Y).inv := by
  apply (cancel_mono (repairedComputationCoprodIso pe J M coherent shared pureInstr X Y).hom).mp
  rw [Iso.inv_hom_id]
  apply coprod.hom_ext
  · rw [inl_coprodComparison_assoc, mapInl, Category.comp_id]
  · rw [inr_coprodComparison_assoc, mapInr, Category.comp_id]

theorem mapDesc {X Y Z : Q} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (F).map (coprod.desc f g) = (repairedComputationCoprodIso pe J M coherent shared pureInstr X Y).hom ≫
      coprod.desc ((F).map f) ((F).map g) := by
  apply (cancel_epi (repairedComputationCoprodIso pe J M coherent shared pureInstr X Y).inv).mp
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp, ← comparison]
  apply coprod.hom_ext
  · rw [inl_coprodComparison_assoc, ← (F).map_comp, coprod.inl_desc, coprod.inl_desc]
  · rw [inr_coprodComparison_assoc, ← (F).map_comp, coprod.inr_desc, coprod.inr_desc]

theorem preservesBinaryCoproducts : PreservesColimitsOfShape (Discrete WalkingPair) (F) := by
  let : ∀ {X Y : Q}, IsIso (coprodComparison (F) X Y) := fun {X Y} => by
    rw [comparison pe J M coherent shared pureInstr X Y]
    infer_instance
  exact preservesBinaryCoproducts_of_isIso_coprodComparison (F)

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.InterpretationCoproductProofs
