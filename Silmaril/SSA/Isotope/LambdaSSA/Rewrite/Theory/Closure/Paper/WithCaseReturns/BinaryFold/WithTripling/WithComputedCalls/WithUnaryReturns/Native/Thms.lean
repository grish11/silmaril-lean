module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.Native

/-! # The printed unary sequence and operator laws as derived rules -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns

open Silmaril.Isotope.LambdaSSA
open CfgEta.TypeCategory (returnRegion)
open Paper.RetainedLet (returnOnce)
open Paper.UnaryReturn (returnOnce_valueBranches)
open Silmaril.DeBruijn (lift)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)
  {Γ : VCtx τ} {A D : τ} {a b : Tm Φ} {L : LCtx τ} {r : Region Φ}

/-- The printed region `let₁-let₁` instance for an arbitrary typed region
body. The saved continuation is weakened below the original result slot. -/
theorem let₁_let₁ (ha : Tm.HasType Γ a A) (hb : Tm.HasType (A :: Γ) b D)
    (hr : HasType (D :: Γ) r L) :
    Eqv pe Γ (.let₁ (.let₁ a b) r) (.let₁ a (.let₁ b (r.renameVars (lift Nat.succ)))) L :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.let₁_let₁ pe ha hb hr

/-- The printed `let₁-op` instance follows using the inherited returned-call
step and unary forwarding with the same typed body. -/
theorem let₁_op (p : Φ) (ha : Tm.HasType Γ a (instrSrc p))
    (hr : HasType (instrTrg p :: Γ) r L) :
    Eqv pe Γ (.let₁ (.op p a) r) (.let₁ a (.let₁ (.op p (.var 0)) (r.renameVars (lift Nat.succ)))) L :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.let₁_op pe p ha hr

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns
