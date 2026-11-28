module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorCaseOperands.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Case.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms

/-! # The common selected-arm denotation -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorCaseOperands

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorCaseOperands
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.SingletonDispatcher (route_inr)
open Silmaril.Isotope.LetIter.Semantics.Categorical (routeEnvironment)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel case_inl_context extend_map)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (extend caseWithContext splitMapCoprod)
open CategoryTheory CategoryTheory.Limits


universe u v u₁ u₂ v₁ v₂
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) (M : TypeModel τ V) [InstructionModel J M Φ]

section Term

variable [DistributiveFreydCategory J]

open scoped MonoidalCategory

private theorem case_inr_context {E A B D : V} (f : J.obj E ⟶ J.obj B)
    (l : J.obj (E ⊗ A) ⟶ J.obj D) (r : J.obj (E ⊗ B) ⟶ J.obj D) :
    caseWithContext J (f ≫ J.map (coprod.inr : B ⟶ A ⨿ B)) l r = extend J f ≫ r := by
  simp only [caseWithContext, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
    Silmaril.Isotope.LetIter.Semantics.Categorical.extend_postmap, Category.assoc]
  rw [← Category.assoc (J.map (DistributiveTensor.leftIso E A B).inv)]
  change extend J f ≫ J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫
    routeEnvironment J E A B ≫ coprod.desc l r = _
  rw [← Category.assoc (J.map _), route_inr J, coprod.inr_desc]

set_option backward.isDefEq.respectTransparency false in
theorem inl_denotes_bind {Γ : VCtx τ} {a l r : Tm Φ} {A B D : τ}
    {ha : Tm.HasType Γ a A} {hl : Tm.HasType (A :: Γ) l D}
    {hr : Tm.HasType (B :: Γ) r D}
    {fa : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)}
    {fl : J.obj (ctxObj M (A :: Γ)) ⟶ J.obj (M.obj D)}
    {fr : J.obj (ctxObj M (B :: Γ)) ⟶ J.obj (M.obj D)}
    (da : Denotes J M ha fa) (dl : Denotes J M hl fl) (dr : Denotes J M hr fr) :
    Denotes J M (.case (.inl ha) hl hr)
      (Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind J fa fl) := by
  have dc := Denotes.case (Denotes.inl da) dl dr
  simp only [Category.assoc, ← J.map_comp, Iso.inv_hom_id, Category.comp_id] at dc
  rwa [case_inl_context J] at dc

set_option backward.isDefEq.respectTransparency false in
theorem inr_denotes_bind {Γ : VCtx τ} {a l r : Tm Φ} {A B D : τ}
    {ha : Tm.HasType Γ a B} {hl : Tm.HasType (A :: Γ) l D}
    {hr : Tm.HasType (B :: Γ) r D}
    {fa : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj B)}
    {fl : J.obj (ctxObj M (A :: Γ)) ⟶ J.obj (M.obj D)}
    {fr : J.obj (ctxObj M (B :: Γ)) ⟶ J.obj (M.obj D)}
    (da : Denotes J M ha fa) (dl : Denotes J M hl fl) (dr : Denotes J M hr fr) :
    Denotes J M (.case (.inr ha) hl hr)
      (Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind J fa fr) := by
  have dc := Denotes.case (Denotes.inr da) dl dr
  simp only [Category.assoc, ← J.map_comp, Iso.inv_hom_id, Category.comp_id] at dc
  rwa [case_inr_context J] at dc

set_option backward.isDefEq.respectTransparency false in
theorem operand_denotes {Γ : VCtx τ} {a b : Tm Φ} {D : τ}
    (h : OperandBeta Γ a b D) (ha : Tm.HasType Γ a D) (hb : Tm.HasType Γ b D) :
    ∃ f, Denotes J M ha f ∧ Denotes J M hb f := by
  cases h with
  | left hp hl hr =>
    obtain ⟨p, dp⟩ := hp.denotes_map J M
    obtain ⟨_, dl⟩ := denotes_exists J M hl
    obtain ⟨_, dr⟩ := denotes_exists J M hr
    obtain ⟨_, ds⟩ := Denotes.substValue J M dp dl
    have dc := inl_denotes_bind J M dp dl dr
    simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, extend_map] at dc
    exact ⟨_, dc, ds⟩
  | right hp hl hr =>
    obtain ⟨p, dp⟩ := hp.denotes_map J M
    obtain ⟨_, dl⟩ := denotes_exists J M hl
    obtain ⟨_, dr⟩ := denotes_exists J M hr
    obtain ⟨_, ds⟩ := Denotes.substValue J M dp dr
    have dc := inr_denotes_bind J M dp dl dr
    simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, extend_map] at dc
    exact ⟨_, dc, ds⟩

private theorem call_denotes {Γ : VCtx τ} {a b : Tm Φ} {D : τ}
    (p : Φ) (h : OperandBeta Γ a b (instrSrc p)) (hout : instrTrg p = D)
    (ha : Tm.HasType Γ (.op p a) D) (hb : Tm.HasType Γ (.op p b) D) :
    ∃ f, Denotes J M ha f ∧ Denotes J M hb f := by
  subst D
  cases ha with
  | op ha =>
    cases hb with
    | op hb =>
      obtain ⟨_, da, db⟩ := operand_denotes J M h ha hb
      exact ⟨_, .op da, .op db⟩

end Term

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]

private theorem subst_typed {Γ : VCtx τ} {a b : Tm Φ} {A B : τ}
    (ha : Tm.HasType Γ a A) (hb : Tm.HasType (A :: Γ) b B) :
    Tm.HasType Γ (b.subst (Tm.singleSubst a)) B := by
  refine Tm.HasType.subst (σ := Tm.singleSubst a) ?_ hb
  intro i D hi
  cases i with
  | zero => cases Option.some.inj hi; exact ha
  | succ i => exact .var hi

theorem operand_typed {Γ : VCtx τ} {a b : Tm Φ} {D : τ} (h : OperandBeta Γ a b D) :
    Tm.HasType Γ a D ∧ Tm.HasType Γ b D := by
  cases h with
  | left hp hl hr => exact ⟨.case (.inl hp.hasType) hl hr, subst_typed hp.hasType hl⟩
  | right hp hl hr => exact ⟨.case (.inr hp.hasType) hl hr, subst_typed hp.hasType hr⟩

theorem step_branches {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (h : Step Γ r s L) :
    ValueBranches Γ r L ∧ ValueBranches Γ s L := by
  cases h with
  | letCall p h hk =>
    obtain ⟨ha, hb⟩ := operand_typed h
    exact ⟨.let₁ (.op ha) hk, .let₁ (.op hb) hk⟩
  | caseCall p h hout hl hr =>
    obtain ⟨ha, hb⟩ := operand_typed h
    exact ⟨.case (hout ▸ Tm.HasType.op ha) hl hr, .case (hout ▸ Tm.HasType.op hb) hl hr⟩

theorem step_denotes {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : Step Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    ∃ f, RegionDenotes J M hr f ∧ RegionDenotes J M hs f := by
  cases h with
  | letCall p h hk =>
    obtain ⟨ha, hb⟩ := operand_typed h
    obtain ⟨_, da, db⟩ := call_denotes J M p h rfl (.op ha) (.op hb)
    obtain ⟨_, dk⟩ := regionDenotes_exists J M hk.hasType
    exact ⟨_, .let₁ da dk, .let₁ db dk⟩
  | caseCall p h hout hl hr =>
    have typed {Γ : VCtx τ} {a : Tm Φ} {D : τ} (ha : Tm.HasType Γ a (instrSrc p))
        (e : instrTrg p = D) : Tm.HasType Γ (.op p a) D := e ▸ .op ha
    obtain ⟨ha, hb⟩ := operand_typed h
    obtain ⟨_, da, db⟩ := call_denotes J M p h hout (typed ha hout) (typed hb hout)
    obtain ⟨_, dl⟩ := regionDenotes_exists J M hl.hasType
    obtain ⟨_, dr⟩ := regionDenotes_exists J M hr.hasType
    exact ⟨_, .case da dl dr, .case db dl dr⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorCaseOperands
