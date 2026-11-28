module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Thms

/-! # Soundness of the exact case-to-bind conversion -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithCaseBind

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Paper.Extension.Singleton (SeedDenotes)
open Paper.RetainedCase (boundCase_hasType denote_boundCase_let)

universe u v u₁ u₂ v₁ v₂

open CfgEta.TypeCategory (returnRegion returnRegion_typed)
open Paper.RetainedLet (returnOnce)
open Paper.RetainedCase (boundCase boundCase_typed)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

theorem case_eq_return_post {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
    (bind : ∀ {Γ L r s}, Paper.WithCaseBind.Step Γ r s L → Seed Γ r s L)
    (unary : ∀ {Γ L r s}, Paper.UnaryReturn.Step Γ r s L → Seed Γ r s L)
    {Γ : VCtx τ} {L : LCtx τ} {A B : τ} {a : Tm Φ} {l r : Region Φ}
    (ha : Tm.HasType Γ a (coprod A B)) (hl : ValueBranches (A :: Γ) l L)
    (hr : ValueBranches (B :: Γ) r L) :
    Paper.Extension.Eqv Seed Γ (.case a l r) ((returnRegion a).lsubst (fun _ => boundCase l r)) L := by
  let e := Paper.WithCaseBind.Step.bind ha hl hr
  have expand : Paper.Extension.Eqv Seed Γ (.case a l r) (.let₁ a (boundCase l r)) L :=
    .extra e.valueBranches.1.hasType e.valueBranches.2.hasType (bind e)
  have post : LSubst.HasType Γ [coprod A B] L (fun _ => boundCase l r) := by
    intro i T hi
    cases i with
    | zero => cases Option.some.inj hi; exact (boundCase_typed hl hr).hasType
    | succ i => simp [At] at hi
  have lowering := (Paper.UnaryReturn.returnRegion_eq_returnOnce unary ha).lsubstPost
    (returnRegion_typed ha) (Paper.UnaryReturn.returnOnce_valueBranches ha) post
  have cancel : (returnOnce a).lsubst (fun _ => boundCase l r) = .let₁ a (boundCase l r) := by
    change Region.let₁ a (compLSubst labelId (fun _ => boundCase l r) 0) = _
    rw [compLSubst_id_left]
  exact expand.trans (cancel ▸ lowering).symm

section Soundness

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

theorem step_denotes : SeedDenotes (Seed := Paper.WithCaseBind.Step (τ := τ) (Φ := Φ)) J M := by
  intro Γ L r s e ht hs
  cases e with
  | bind ha hl hr =>
    have eq := denote_boundCase_let J M ha hl.hasType hr.hasType
    change denoteRegion J M hs = denoteRegion J M ht at eq
    exact ⟨_, denoteRegion_spec J M ht, eq ▸ denoteRegion_spec J M hs⟩

end Soundness

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithCaseBind
