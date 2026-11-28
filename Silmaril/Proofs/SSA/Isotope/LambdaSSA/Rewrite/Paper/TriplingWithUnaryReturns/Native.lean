module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.BranchNormalization.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns

open Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns (Eqv lowering)

open Silmaril.Isotope.LambdaSSA
open CfgEta.TypeCategory (returnRegion)
open Paper.RetainedLet (returnOnce)
open Paper.UnaryReturn (returnOnce_valueBranches)
open Silmaril.DeBruijn (lift)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)
  {Γ : VCtx τ} {A D : τ} {a b : Tm Φ} {L : LCtx τ} {r : Region Φ}

private theorem forward
    {t : Tm Φ} (ht : Tm.HasType Γ t D) (ha : Tm.HasType Γ a A) (hb : Tm.HasType (A :: Γ) b D)
    (rewrite : Eqv pe Γ (returnOnce t) (.let₁ a (returnOnce b)) [D]) (hr : HasType (D :: Γ) r L) :
    Eqv pe Γ (.let₁ t r) (.let₁ a (.let₁ b (r.renameVars (lift Nat.succ)))) L := by
  have typed : LSubst.HasType Γ [D] L (fun _ => r) := by
    intro i T hi
    cases i with
    | zero => cases Option.some.inj hi; exact hr
    | succ i => simp [At] at hi
  have post := Paper.Extension.Eqv.lsubstPost rewrite
    (returnOnce_valueBranches ht) (.let₁ ha (returnOnce_valueBranches hb)) typed
  change Eqv pe Γ ((Region.br 0 t).bindBranchArguments.lsubst (fun _ => r))
    (.let₁ a ((Region.br 0 b).bindBranchArguments.lsubst (liftLSubstVars (fun _ => r)))) L at post
  rw [lsubst_bindBranchArguments_br, lsubst_bindBranchArguments_br] at post
  exact post

theorem let₁_let₁ (ha : Tm.HasType Γ a A) (hb : Tm.HasType (A :: Γ) b D)
    (hr : HasType (D :: Γ) r L) :
    Eqv pe Γ (.let₁ (.let₁ a b) r) (.let₁ a (.let₁ b (r.renameVars (lift Nat.succ)))) L := by
  let seed := Paper.UnaryReturn.Step.fuse ha hb
  exact forward pe (.let₁ ha hb) ha hb (.symm (.extra seed.typed.1 seed.typed.2 (.inr seed))) hr

theorem let₁_op (p : Φ) (ha : Tm.HasType Γ a (instrSrc p))
    (hr : HasType (instrTrg p :: Γ) r L) :
    Eqv pe Γ (.let₁ (.op p a) r) (.let₁ a (.let₁ (.op p (.var 0)) (r.renameVars (lift Nat.succ)))) L := by
  let hb : Tm.HasType (instrSrc p :: Γ) (.op p (.var 0)) (instrTrg p) := .op (.var (i := 0) rfl)
  let seed := Paper.UnaryReturn.Step.fuse ha hb
  have call : Eqv pe Γ (returnOnce (.op p a)) (returnRegion (.let₁ a (.op p (.var 0)))) [instrTrg p] :=
    (Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.computedCall pe p ha).mapSeed Or.inl
  exact forward pe (.op ha) ha hb
    (call.trans ((lowering pe (.let₁ ha hb)).trans (.symm (.extra seed.typed.1 seed.typed.2 (.inr seed))))) hr

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns
