module

public import Silmaril.SSA.Isotope.LambdaSSA.Subtyping.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms

@[expose] public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA.Subtyping.Semantics.Categorical

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
  (ctxObj lookup ctxPairIso labelObj labelInject finiteLabelObj labelObjToFinite
    labelAppendSplit CollectiveDenotes)

open Silmaril.Isotope.LambdaSSA.Semantics.Categorical (collectiveDenotes_exists_succ collective_ext)

section Term

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ]
  (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

theorem denote_spec_proof {Γ : VCtx τ} {t : LambdaSSA.Tm Φ} {A : τ}
    (h : Tm.HasType Γ t A) : Denotes J M h (denote J M h) := by
  induction h with
  | var h => exact .var h
  | op _ ih => exact .op ih
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | pair _ _ iha ihb => exact .pair iha ihb
  | unit => exact .unit
  | let₂ _ _ iha ihb => exact .let₂ iha ihb
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ihe ihl ihr => exact .case ihe ihl ihr
  | abort _ ih => exact .abort ih
  | sub _ d ih => exact .sub ih d

theorem denote_unique_proof {Γ : VCtx τ} {t : LambdaSSA.Tm Φ} {A : τ}
    {h : Tm.HasType Γ t A} {f : J.obj (ctxObj (exactTypeModel M) Γ) ⟶ J.obj (M.obj A)}
    (d : Denotes J M h f) : f = denote J M h := by
  induction d <;> simp only [denote, *]

end Term

section Region

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ]
  (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

theorem regionDenotes_exists_proof { Γ : VCtx τ} {r : LambdaSSA.Region Φ} {L : LCtx τ}
    (h : Region.HasType Γ r L) : ∃ f, RegionDenotes J M h f := by
  induction h with
  | br h ha => exact ⟨_, .br (h := h) (denote_spec_proof J M ha)⟩
  | case he hl hr ihl ihr =>
      rcases ihl with ⟨fl, dl⟩
      rcases ihr with ⟨fr, dr⟩
      exact ⟨_, .case (denote_spec_proof J M he) dl dr⟩
  | let₁ ha hb ih =>
      rcases ih with ⟨fb, db⟩
      exact ⟨_, .let₁ (denote_spec_proof J M ha) db⟩
  | let₂ ha hb ih =>
      rcases ih with ⟨fb, db⟩
      exact ⟨_, .let₂ (denote_spec_proof J M ha) db⟩
  | @cfg _ _ _ n _ R he hb ihe ihb =>
      cases n with
      | zero =>
          rcases ihe with ⟨fe, de⟩
          exact ⟨fe, .cfgZero de⟩
      | succ n =>
          rcases ihe with ⟨fe, de⟩
          choose fb db using ihb
          rcases collectiveDenotes_exists_succ J (exactTypeModel M) n _ R _ fb with ⟨fc, dc⟩
          exact ⟨_, .cfg de db dc⟩

theorem regionDenotes_unique_proof {Γ : VCtx τ} {r : LambdaSSA.Region Φ} {L : LCtx τ}
    {h : Region.HasType Γ r L}
    {f g : J.obj (ctxObj (exactTypeModel M) Γ) ⟶ J.obj (labelObj (exactTypeModel M) L)}
    (d : RegionDenotes J M h f) (e : RegionDenotes J M h g) : f = g := by
  induction d with
  | br da =>
      cases e with
      | br ea => rw [denote_unique_proof J M da, denote_unique_proof J M ea]
  | case de dl dr ihl ihr =>
      cases e with
      | case ee el er =>
          rw [denote_unique_proof J M de, denote_unique_proof J M ee, ihl el, ihr er]
  | let₁ da db ih =>
      cases e with
      | let₁ ea eb => rw [denote_unique_proof J M da, denote_unique_proof J M ea, ih eb]
  | let₂ da db ih =>
      cases e with
      | let₂ ea eb => rw [denote_unique_proof J M da, denote_unique_proof J M ea, ih eb]
  | cfgZero de ih =>
      cases e with
      | cfgZero ee => exact ih ee
  | cfg de db dc ihe ihb =>
      cases e with
      | cfg ee eb ec =>
          have entry_eq := ihe ee
          have collective_eq := collective_ext J (exactTypeModel M) _ _ _ fun i =>
            (dc.restrict i).trans ((ihb i (eb i)).trans (ec.restrict i).symm)
          rw [entry_eq, collective_eq]

end Region

end Silmaril.Isotope.LambdaSSA.Subtyping.Semantics.Categorical
