module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithLetCase.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.BranchNormalization.Thms

/-! # The printed continuation equation from a singleton return -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithLetCase

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithLetCase
open Paper.RetainedLet (returnOnce)
open Silmaril.DeBruijn (lift)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

theorem distributed_typed {Γ : VCtx τ} {L : LCtx τ} {A B D : τ} {e a b : Tm Φ} {k : Region Φ}
    (he : Tm.HasType Γ e (coprod A B)) (ha : Tm.HasType (A :: Γ) a D)
    (hb : Tm.HasType (B :: Γ) b D) (hk : HasType (D :: Γ) k L) :
    HasType Γ (distributed e a b k) L :=
  .case he (.let₁ ha (hk.renameVars ((Ren.wk Γ A).lift D)))
    (.let₁ hb (hk.renameVars ((Ren.wk Γ B).lift D)))

theorem distributed_valueBranches {Γ : VCtx τ} {L : LCtx τ}
    {A B D : τ} {e a b : Tm Φ} {k : Region Φ}
    (he : Tm.HasType Γ e (coprod A B)) (ha : Tm.HasType (A :: Γ) a D)
    (hb : Tm.HasType (B :: Γ) b D) (hk : ValueBranches (D :: Γ) k L) :
    ValueBranches Γ (distributed e a b k) L :=
  .case he (.let₁ ha (hk.renameVars ((Ren.wk Γ A).lift D)))
    (.let₁ hb (hk.renameVars ((Ren.wk Γ B).lift D)))

private theorem post_returnOnce (x : Tm Φ) (σ : Nat → Region Φ) :
    (returnOnce x).lsubst σ = .let₁ x (σ 0) := by
  change ((Region.br 0 x).bindBranchArguments.lsubst σ) = _
  exact lsubst_bindBranchArguments_br 0 x σ

theorem of_return {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
    {Γ : VCtx τ} {L : LCtx τ} {A B D : τ} {e a b : Tm Φ} {k : Region Φ}
    (he : Tm.HasType Γ e (coprod A B)) (ha : Tm.HasType (A :: Γ) a D)
    (hb : Tm.HasType (B :: Γ) b D) (hk : HasType (D :: Γ) k L)
    (h : Paper.Extension.Eqv Seed Γ (returnOnce (.case e a b))
      (.case e (returnOnce a) (returnOnce b)) [D]) :
    Paper.Extension.Eqv Seed Γ (.let₁ (.case e a b) k) (distributed e a b k) L := by
  let endpoints := (Step.split he ha hb).valueBranches
  have typed : LSubst.HasType Γ [D] L (fun _ => k) :=
    fun _ _ h => (List.mem_singleton.mp (List.mem_of_getElem? h)).symm ▸ hk
  have post := Paper.Extension.Eqv.lsubstPost h endpoints.1 endpoints.2 typed
  rw [post_returnOnce] at post
  change Paper.Extension.Eqv Seed Γ (.let₁ (.case e a b) k)
    (.case e ((returnOnce a).lsubst (Region.liftLSubstVars (fun _ => k)))
      ((returnOnce b).lsubst (Region.liftLSubstVars (fun _ => k)))) L at post
  rw [post_returnOnce, post_returnOnce] at post
  exact post

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithLetCase
