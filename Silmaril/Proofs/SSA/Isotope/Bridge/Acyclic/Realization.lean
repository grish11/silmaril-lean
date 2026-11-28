module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Categorical.Realization.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Case.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Naturality.Thms

public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Acyclic

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped MonoidalCategory
open LetIter.Semantics.Categorical
  (TypeModel InstructionModel envObj envSnocIso envPairHom boundVar boundLookup boundObj
    bind_pre_map pair_pre_map case_pre_map)
open LetIter.ProofRelevant.Semantics.Categorical (caseWithContext extend)
open LambdaSSA.Semantics.Categorical
open Morphism.CaseSSA (erase erase_hasType)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (M : TypeModel τ V)

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

omit [HasTy Φ τ] in
theorem contextMap_isIso_proof {n : Nat} (β : BoundCtx τ n) : IsIso (contextMap M β) := by
  induction β with
  | nil => exact inferInstanceAs (IsIso (λ_ (𝟙_ V)).inv)
  | snoc β A ih =>
    let _ := ih
    exact inferInstanceAs (IsIso ((contextMap M β ▷ M.obj A) ≫
      (envSnocIso M Γ₀ β A).hom))

private theorem lookup_contextMap {n : Nat} (β : BoundCtx τ n) (i : Fin n) :
    contextMap M β ≫ boundVar M (Γ := Γ₀) i =
      lookup M i.val (BoundCtx.getElem?_toList β i) := by
  induction β with
  | nil => exact i.elim0
  | snoc β A ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · change ((_ ▷ M.obj A) ≫ (α_ _ _ _).hom) ≫ snd _ _ ≫ snd _ _ = snd _ _
        rw [Category.assoc, associator_hom_snd_snd, whiskerRight_snd]
      · change ((_ ▷ M.obj A) ≫ (α_ _ _ _).hom) ≫ snd _ _ ≫
          fst _ _ ≫ boundLookup M j = fst _ _ ≫ lookup M j.val _
        rw [Category.assoc, associator_hom_snd_fst_assoc, whiskerRight_fst_assoc,
          ← Category.assoc, ← ih j]
        rw [Category.assoc, boundVar]

private theorem contextMap_pair {n : Nat} (β : BoundCtx τ n) (A B : τ) :
    (ctxPairIso M β.toList A B).hom ≫ contextMap M ((β.snoc A).snoc B) =
      (contextMap M β ▷ (M.obj A ⊗ M.obj B)) ≫ envPairHom M Γ₀ β A B := by
  have expand : envPairHom M Γ₀ β A B =
      (α_ (envObj M Γ₀ β) (M.obj A) (M.obj B)).inv ≫
        (envSnocIso M Γ₀ β A).hom ▷ M.obj B ≫ (envSnocIso M Γ₀ (β.snoc A) B).hom :=
    MonoidalCategory.pentagon_inv_hom_hom_hom_inv.symm
  rw [expand]
  simp only [ctxPairIso, Iso.symm_hom, contextMap, MonoidalCategory.comp_whiskerRight,
    Category.assoc, MonoidalCategory.associator_inv_naturality_left_assoc]

variable {C : Type u₂} [Category.{v₂} C] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C)

local notation "denoteCase" => LetCase.Semantics.Categorical.denote J M
local notation "bindArrow" => LetIter.ProofRelevant.Semantics.Categorical.bind

section Operands

variable [DistributiveFreydCategory J] [InstructionModel J M Φ]

omit [DistributiveFreydCategory J] [SymmetricCategory V] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C] [HasFiniteCoproducts C] [DistributiveTensor V]
  [DistributivePremonoidalCategory C] in
private theorem map_context_snoc {n : Nat} (β : BoundCtx τ n) (A : τ) :
    J.map (contextMap M (β.snoc A)) =
      J.map (contextMap M β ▷ M.obj A) ≫ J.map (envSnocIso M Γ₀ β A).hom :=
  J.map_comp _ _

private theorem context_bind {n : Nat} {β : BoundCtx τ n} {A : τ} {X : V}
    (f : J.obj (envObj M Γ₀ β) ⟶ J.obj (M.obj A))
    (g : J.obj (envObj M Γ₀ (β.snoc A)) ⟶ J.obj X) :
    bindArrow J (J.map (contextMap M β) ≫ f) (J.map (contextMap M (β.snoc A)) ≫ g) =
      J.map (contextMap M β) ≫ bindArrow J f (J.map (envSnocIso M Γ₀ β A).hom ≫ g) := by
  rw [map_context_snoc, Category.assoc, bind_pre_map]

private theorem context_bind_pair {n : Nat} {β : BoundCtx τ n} {A B : τ} {X : V}
    (f : J.obj (envObj M Γ₀ β) ⟶ J.obj (M.obj (product A B)))
    (g : J.obj (envObj M Γ₀ ((β.snoc A).snoc B)) ⟶ J.obj X) :
    bindArrow J (J.map (contextMap M β) ≫ f)
      (J.map ((𝟙 _) ⊗ₘ (M.productIso A B).hom) ≫ J.map (ctxPairIso M β.toList A B).hom ≫
        J.map (contextMap M ((β.snoc A).snoc B)) ≫ g) =
      J.map (contextMap M β) ≫ bindArrow J f (J.map ((𝟙 _) ⊗ₘ (M.productIso A B).hom) ≫
        J.map (envPairHom M Γ₀ β A B) ≫ g) := by
  rw [← J.map_comp_assoc (ctxPairIso M β.toList A B).hom, contextMap_pair,
    J.map_comp_assoc, ← J.map_comp_assoc, MonoidalCategory.id_tensorHom,
    MonoidalCategory.whisker_exchange, J.map_comp_assoc, bind_pre_map, MonoidalCategory.id_tensorHom]

private theorem context_case {n : Nat} {β : BoundCtx τ n} {A B : τ} {X : V}
    (f : J.obj (envObj M Γ₀ β) ⟶ J.obj (M.obj (coprod A B)))
    (l : J.obj (envObj M Γ₀ (β.snoc A)) ⟶ J.obj X)
    (r : J.obj (envObj M Γ₀ (β.snoc B)) ⟶ J.obj X) :
    caseWithContext J ((J.map (contextMap M β) ≫ f) ≫ J.map (M.coprodIso A B).hom)
      (J.map (contextMap M (β.snoc A)) ≫ l) (J.map (contextMap M (β.snoc B)) ≫ r) =
      J.map (contextMap M β) ≫ caseWithContext J (f ≫ J.map (M.coprodIso A B).hom)
        (J.map (envSnocIso M Γ₀ β A).hom ≫ l) (J.map (envSnocIso M Γ₀ β B).hom ≫ r) := by
  simp only [map_context_snoc, Category.assoc]
  exact case_pre_map J _ _ _ _

theorem operandDenotes_proof {n : Nat} {β : BoundCtx τ n} {A : τ}
    {t : LetCase.LocallyNameless.Tm Empty Φ n}
    (d : LetCase.LocallyNameless.Derivation Φ Γ₀ β t A) :
    Denotes J M (erase_hasType d.toHasType)
      (J.map (contextMap M β) ≫ denoteCase d) := by
  induction d with
  | @fv _ _ x => exact x.elim
  | bv =>
      rw [LetCase.Semantics.Categorical.denote, ← J.map_comp, lookup_contextMap]
      exact .var _
  | op _ ih =>
      rw [LetCase.Semantics.Categorical.denote, ← Category.assoc]
      exact .op ih
  | unit =>
      rw [LetCase.Semantics.Categorical.denote, ← J.map_comp, ← Category.assoc]
      rw [show contextMap M _ ≫ toUnit _ = toUnit _ from isTerminalTensorUnit.hom_ext _ _]
      exact .unit
  | let₁ _ _ iha ihb =>
      rw [LetCase.Semantics.Categorical.denote, ← context_bind]
      exact .let₁ iha ihb
  | pair _ _ iha ihb =>
      rw [LetCase.Semantics.Categorical.denote, ← Category.assoc, ← pair_pre_map]
      exact .pair iha ihb
  | let₂ _ _ iha ihb =>
      rw [LetCase.Semantics.Categorical.denote, ← context_bind_pair]
      exact .let₂ iha ihb
  | inl _ ih =>
      rw [LetCase.Semantics.Categorical.denote, ← Category.assoc]
      exact .inl ih
  | inr _ ih =>
      rw [LetCase.Semantics.Categorical.denote, ← Category.assoc]
      exact .inr ih
  | case _ _ _ ihe ihl ihr =>
      rw [LetCase.Semantics.Categorical.denote, ← context_case]
      exact .case ihe ihl ihr
  | abort _ ih =>
      rw [LetCase.Semantics.Categorical.denote, ← Category.assoc]
      exact .abort ih

end Operands

section Regions

open LetIter.Semantics.Categorical (case_inl_context case_postcomp contextualLoop_fixpoint extend_postmap)
open LetIter.ProofRelevant.Semantics.Categorical (contextualLoop duplicate)
open SingletonDispatcher (denoteSingleCfg caseWithContext_inr labelAppendSplit_zero
  labelAppendSplit_succ labelInject_payload)

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] [InstructionModel J M Φ]
  [RegionTypingCoherent (Φ := Φ) J M]

omit [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M] in
private theorem loop_exit {R S X : V} (f : J.obj (R ⊗ S) ⟶ J.obj X) :
    contextualLoop J (f ≫ J.map (coprod.inl : X ⟶ X ⨿ S)) = f := by
  rw [contextualLoop_fixpoint, case_inl_context, LetIter.ProofRelevant.Semantics.Categorical.bind]
  simp only [extend, PremonoidalCategory.leftTensor, PremonoidalCategory.id_whiskerRight,
    Category.id_comp, Category.assoc]
  rw [FreydCategory.whiskerLeft_snd J, ← J.map_comp_assoc]
  simp [duplicate]

theorem denote_toSSA_proof {n : Nat} {β : BoundCtx τ n} {A : τ}
    (c : Code Φ β A) {L : LCtx τ} {exit : Nat} (h : At L exit A) :
    denoteRegion J M (c.toSSA_hasType h) =
      J.map (contextMap M β) ≫ denoteCase c.toLetCase.2 ≫ J.map (labelInject M exit h) := by
  induction c generalizing L exit with
  | br a =>
      rw [← Category.assoc]
      exact ((RegionDenotes.br (h := h) (operandDenotes_proof M J a.2)).eq_denote J M).symm
  | let₁ a b ih =>
      have db := denoteRegion_spec J M (b.toSSA_hasType h)
      rw [ih h] at db
      rw [← (RegionDenotes.let₁ (operandDenotes_proof M J a.2) db).eq_denote J M]
      simpa only [Code.toLetCase, LetCase.Semantics.Categorical.denote,
        LetIter.ProofRelevant.Semantics.Categorical.bind, Category.assoc] using
        context_bind M J (denoteCase a.2) (denoteCase b.toLetCase.2 ≫ J.map (labelInject M exit h))
  | let₂ a b ih =>
      have db := denoteRegion_spec J M (b.toSSA_hasType h)
      rw [ih h] at db
      rw [← (RegionDenotes.let₂ (operandDenotes_proof M J a.2) db).eq_denote J M]
      simpa only [Code.toLetCase, LetCase.Semantics.Categorical.denote,
        LetIter.ProofRelevant.Semantics.Categorical.bind, Category.assoc] using
        context_bind_pair M J (denoteCase a.2)
          (denoteCase b.toLetCase.2 ≫ J.map (labelInject M exit h))
  | case e l r ihl ihr =>
      have dl := denoteRegion_spec J M (l.toSSA_hasType h)
      have dr := denoteRegion_spec J M (r.toSSA_hasType h)
      rw [ihl h] at dl
      rw [ihr h] at dr
      rw [← (RegionDenotes.case (operandDenotes_proof M J e.2) dl dr).eq_denote J M]
      simpa only [Code.toLetCase, LetCase.Semantics.Categorical.denote, Category.assoc,
        case_postcomp] using
        context_case M J (denoteCase e.2) (denoteCase l.toLetCase.2 ≫ J.map (labelInject M exit h))
          (denoteCase r.toLetCase.2 ≫ J.map (labelInject M exit h))
  | @join _ β D E entry block ihe ihb =>
      let he := entry.toSSA_hasType (L := D :: L) (exit := 0) (A := D) rfl
      let hb := block.toSSA_hasType (L := D :: L) (exit := exit + 1) h
      let f := J.map (contextMap M β) ≫ denoteCase entry.toLetCase.2
      let g := J.map (contextMap M (β.snoc D)) ≫ denoteCase block.toLetCase.2
      let inject := labelInject M exit h
      let localLabel := labelInject M 0 (L := [D]) (A := D) rfl
      let load := J.map (ctxObj M β.toList ◁ singletonLabelPayload M D)
      have entry_split : denoteRegion J M he ≫ J.map (labelAppendSplit M [D] L) =
          (f ≫ J.map localLabel) ≫ J.map coprod.inr := by
        rw [ihe (L := D :: L) (exit := 0) rfl]
        simp only [f, localLabel, Category.assoc, ← J.map_comp,
          labelAppendSplit_zero]
      have block_split : denoteRegion J M hb ≫ J.map (labelAppendSplit M [D] L) =
          (g ≫ J.map inject) ≫ J.map coprod.inl := by
        rw [ihb (L := D :: L) (exit := exit + 1) h]
        simp only [g, inject, Category.assoc, ← J.map_comp,
          labelAppendSplit_succ]
      rw [show denoteRegion J M ((Code.join entry block).toSSA_hasType h) =
          denoteRegion J M (.cfg (fun _ : Fin 1 => D) he (fun _ => hb)) from rfl,
        denoteSingleCfg M J he hb, entry_split, caseWithContext_inr]
      change extend J (f ≫ J.map localLabel) ≫
        contextualLoop J (load ≫ denoteRegion J M hb ≫ J.map (labelAppendSplit M [D] L)) = _
      rw [block_split, ← Category.assoc load, loop_exit, extend_postmap, Category.assoc]
      change extend J f ≫ J.map (ctxObj M β.toList ◁ localLabel) ≫
        J.map (ctxObj M β.toList ◁ singletonLabelPayload M D) ≫ g ≫ J.map inject = _
      rw [← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp, labelInject_payload,
        MonoidalCategory.whiskerLeft_id, J.map_id, Category.id_comp]
      simpa only [Code.toLetCase, LetCase.Semantics.Categorical.denote, f, g, inject,
        LetIter.ProofRelevant.Semantics.Categorical.bind, Category.assoc] using
        context_bind M J (denoteCase entry.toLetCase.2)
          (denoteCase block.toLetCase.2 ≫ J.map inject)

end Regions

end Silmaril.Isotope.LambdaSSA.Acyclic
