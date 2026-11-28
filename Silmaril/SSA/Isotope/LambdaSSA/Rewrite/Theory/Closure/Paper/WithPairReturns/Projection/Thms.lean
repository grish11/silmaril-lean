module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PairSecondProjection

/-! # Sequencing a returned pair and projecting the second field -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns

open Silmaril
open CfgEta.TypeCategory (returnRegion)

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}

local notation "E" => Paper.Extension.Eqv Seed

/-- Returning the second field evaluates the left operand and then the right
operand, retaining the original input for the right computation. -/
theorem return_pair_second
    (pair : ∀ {Γ L r s}, Paper.WithPairReturns.Step Γ r s L → Seed Γ r s L)
    (projection : ∀ {Γ L r s}, Paper.WithProjectionReturns.Step Γ r s L → Seed Γ r s L)
    {Γ : VCtx τ} {A B : τ} {a b : Tm Φ}
    (ha : Tm.HasType Γ a A) (hb : Tm.HasType Γ b B) :
    E Γ (returnRegion (.let₁ (.pair a b) (.let₂ (.var 0) (.var 0))))
      (.let₁ a (.let₁ (b.rename Nat.succ) (.br 0 (.var 0)))) [B] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PairSecondProjection.return_pair_second pair projection ha hb

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns
