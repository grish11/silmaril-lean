module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Naturality.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Coherence.Defs

/-! # Forgetting anonymous free slots in native LetIter denotation -/

public section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped MonoidalCategory
open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation Tm)
open Silmaril.Isotope.LetIter.Semantics.Categorical
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext contextualLoop)
local notation "bindArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.TypingCoherenceProofs
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Erase only the free context, preserving all intermediate typing choices. -/
private def withoutFree {Γ : Ctx Empty τ} :
    ∀ {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {A : τ},
      Derivation Φ Γ β t A → Derivation Φ (Ctx.nil : Ctx Empty τ) β t A
  | _, _, _, _, .fv (x := x) _ => x.elim
  | _, _, _, _, .bv => .bv
  | _, _, _, _, .op d => .op (withoutFree d)
  | _, _, _, _, .let₁ d e => .let₁ (withoutFree d) (withoutFree e)
  | _, _, _, _, .unit => .unit
  | _, _, _, _, .pair d e => .pair (withoutFree d) (withoutFree e)
  | _, _, _, _, .let₂ d e => .let₂ (withoutFree d) (withoutFree e)
  | _, _, _, _, .inl d => .inl (withoutFree d)
  | _, _, _, _, .inr d => .inr (withoutFree d)
  | _, _, _, _, .case d l r => .case (withoutFree d) (withoutFree l) (withoutFree r)
  | _, _, _, _, .abort d => .abort (withoutFree d)
  | _, _, _, _, .iter d e => .iter (withoutFree d) (withoutFree e)

section
variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (M : TypeModel τ V) (Γ : Ctx Empty τ)

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)
local notation "VΓ" => ctxObj M Γ
local notation "V₀" => (𝟙_ V)

private def forgetFree {n : Nat} (β : BoundCtx τ n) : envObj M Γ β ⟶ envObj M Γ₀ β :=
  toUnit VΓ ▷ boundObj M β

@[reassoc] private theorem forgetSnoc {n : Nat} (β : BoundCtx τ n) (A : τ) :
    (envSnocIso M Γ β A).hom ≫ forgetFree M Γ (.snoc β A) =
      (forgetFree M Γ β ▷ M.obj A) ≫ (envSnocIso M Γ₀ β A).hom :=
  (MonoidalCategory.associator_naturality_left (toUnit VΓ) (boundObj M β) (M.obj A)).symm

@[reassoc] private theorem forgetPair {n : Nat} (β : BoundCtx τ n) (A B : τ) :
    envPairHom M Γ β A B ≫ forgetFree M Γ (.snoc (.snoc β A) B) =
      (forgetFree M Γ β ▷ (M.obj A ⊗ M.obj B)) ≫ envPairHom M Γ₀ β A B := by
  unfold envPairHom
  simp only [Category.assoc]
  change (α_ VΓ (boundObj M β) (M.obj A ⊗ M.obj B)).hom ≫
      (VΓ ◁ (α_ (boundObj M β) (M.obj A) (M.obj B)).inv) ≫
      (toUnit VΓ ▷ ((boundObj M β ⊗ M.obj A) ⊗ M.obj B)) =
    ((toUnit VΓ ▷ boundObj M β) ▷ (M.obj A ⊗ M.obj B)) ≫
      (α_ V₀ (boundObj M β) (M.obj A ⊗ M.obj B)).hom ≫
      (V₀ ◁ (α_ (boundObj M β) (M.obj A) (M.obj B)).inv)
  rw [MonoidalCategory.whisker_exchange, MonoidalCategory.associator_naturality_left_assoc]

end

section
variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

private theorem denote_forgetFree {Γ : Ctx Empty τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm Empty Φ n} {A : τ} (d : Derivation Φ Γ β t A) :
    denote J M d = J.map (forgetFree M Γ β) ≫ denote J M (withoutFree d) := by
  induction d with
  | @fv _ _ x _ _ => exact x.elim
  | @bv n β i =>
    simp only [withoutFree, denote, ← Functor.map_comp, boundVar, forgetFree]
    apply congrArg J.map
    change _ = (toUnit (ctxObj M Γ) ▷ boundObj M β) ≫ snd (𝟙_ V) (boundObj M β) ≫ boundLookup M i
    rw [whiskerRight_snd_assoc]
  | unit =>
    simp only [withoutFree, denote, ← Functor.map_comp, ← Category.assoc]
    congr 2
    exact isTerminalTensorUnit.hom_ext _ _
  | op _ ih | inl _ ih | inr _ ih | abort _ ih =>
    simp only [withoutFree, denote, ih, Category.assoc]
  | pair _ _ ih₁ ih₂ =>
    simp only [withoutFree, denote, ih₁, ih₂, pair_pre_map, Category.assoc]
  | let₁ _ _ ih₁ ih₂ =>
    simp only [withoutFree, denote, ih₁, ih₂]
    rw [← J.map_comp_assoc, forgetSnoc, J.map_comp_assoc, bind_pre_map]
  | @let₂ _ β _ _ A B _ _ _ ih₁ ih₂ =>
    simp only [withoutFree, denote, ih₁, ih₂, MonoidalCategory.id_tensorHom]
    rw [← J.map_comp_assoc (envPairHom M Γ β A B), forgetPair, J.map_comp_assoc,
      ← J.map_comp_assoc, MonoidalCategory.whisker_exchange, J.map_comp_assoc, bind_pre_map]
  | case _ _ _ ih₁ ih₂ ih₃ =>
    simp only [withoutFree, denote, ih₁, ih₂, ih₃, Category.assoc]
    rw [← J.map_comp_assoc, forgetSnoc, J.map_comp_assoc,
      ← J.map_comp_assoc (envSnocIso M Γ _ _).hom, forgetSnoc, J.map_comp_assoc, case_pre_map]
  | iter _ _ ih₁ ih₂ =>
    simp only [withoutFree, denote, ih₁, ih₂, Category.assoc]
    rw [← J.map_comp_assoc, forgetSnoc, J.map_comp_assoc, contextualLoop_pre_map, bind_pre_map]

/-- Coherence with no free names is determined by the empty free context.
The arbitrary free context may still have anonymous value slots. -/
theorem typingCoherent_empty_of_nil
    (h : ∀ {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {A : τ}
      (d e : Derivation Φ Γ₀ β t A), denote J M d = denote J M e) :
    TypingCoherent (ν := Empty) J M Φ := by
  intro Γ n β t A d e
  rw [denote_forgetFree J M d, denote_forgetFree J M e, h]

end

end Silmaril.Isotope.LetIter.Semantics.Categorical.TypingCoherenceProofs
