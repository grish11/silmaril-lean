module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.BranchNormalization.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Outward.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.OutwardEffect

/-! # Branch normalization preserves exact typing and categorical denotation -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits

theorem bindBranchArguments_valueBranches
    {τ : Type u₃} [TypeFormers τ] {Φ : Type u₄} [HasTy Φ τ]
    {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ} (hr : Region.HasType Γ r L) :
    Region.ValueBranches Γ r.bindBranchArguments L := by
  induction hr with
  | br hℓ ha => exact .let₁ ha (.br hℓ (.var rfl))
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ ihl ihr => exact .case ha ihl ihr
  | cfg R _ _ ihe ihb => exact .cfg R ihe ihb

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

theorem bindBranchArguments_common
    (hu : PremonoidalCategory.IsCentral (Functor.StrongPremonoidal.unitIso (J := J)).hom)
    {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ} (hr : Region.HasType Γ r L) :
    ∃ (hs : Region.HasType Γ r.bindBranchArguments L), ∃ f,
      RegionDenotes J M hr f ∧ RegionDenotes J M hs f := by
  induction hr with
  | br hℓ ha => exact ⟨.let₁ ha (.br hℓ (.var rfl)), branchBind_common J M hu hℓ ha⟩
  | let₁ ha _ ih =>
      obtain ⟨_, _, dr, ds⟩ := ih
      have da := denote_spec J M ha
      exact ⟨_, _, .let₁ da dr, .let₁ da ds⟩
  | let₂ ha _ ih =>
      obtain ⟨_, _, dr, ds⟩ := ih
      have da := denote_spec J M ha
      exact ⟨_, _, .let₂ da dr, .let₂ da ds⟩
  | case ha _ _ ihl ihr =>
      obtain ⟨_, _, dl, dl'⟩ := ihl
      obtain ⟨_, _, dr, dr'⟩ := ihr
      have da := denote_spec J M ha
      exact ⟨_, _, .case da dl dr, .case da dl' dr'⟩
  | @cfg _ _ _ n _ R he hb ihe ihb =>
      obtain ⟨he', fe, de, de'⟩ := ihe
      choose hb' fb db using ihb
      cases n with
      | zero => exact ⟨.cfg R he' hb', fe, .cfgZero he hb de, .cfgZero he' hb' de'⟩
      | succ n =>
          obtain ⟨_, dc⟩ := collectiveDenotes_exists_succ J M n _ R _ fb
          exact ⟨.cfg R he' hb', _, .cfg he hb de (fun i => (db i).1) dc,
            .cfg he' hb' de' (fun i => (db i).2) dc⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
