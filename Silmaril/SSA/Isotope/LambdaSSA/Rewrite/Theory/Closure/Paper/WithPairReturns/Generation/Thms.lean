module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Generation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Generation.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PairReturnFragment

/-! # Generation of singleton returns with pairs and projections -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns

open Silmaril Silmaril.Isotope.LambdaSSA
open CfgEta.TypeCategory (returnRegion_typed)
open Paper.Extension.Singleton (ofRegion productFst productSnd)
open Paper.Extension.Singleton.Generation (Generated)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "Seed" => JoinedStep (τ := τ) (Φ := Φ) pe

/-- Returning the direct first projection is the guarded first projection arrow. -/
theorem returnFst_eq_productFst (A B : τ) :
    ofRegion Seed (returnRegion_typed (WithProjectionReturns.fstTerm A B)) = productFst Seed A B :=
  PairReturnFragment.returnFst_eq_productFst pe Seed (fun step => step) A B

/-- Returning the direct second projection is the guarded second projection arrow. -/
theorem returnSnd_eq_productSnd (A B : τ) :
    ofRegion Seed (returnRegion_typed (WithProjectionReturns.sndTerm A B)) = productSnd Seed A B :=
  PairReturnFragment.returnSnd_eq_productSnd pe Seed (fun step => step) A B

/-- The recursive return proof uses each additional equation only when
its corresponding constructor is enabled. -/
theorem generated_returnFragment_with_rules
    (S : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
    (includeJoin : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}, Seed Γ r s L → S Γ r s L)
    {computedCalls productReturns : Bool} (calls : computedCalls = true → CallReturnAgreement S)
    (products : productReturns = true → ProductReturnAgreement S)
    {X D : τ} {t : Tm Φ} {ht : Tm.HasType [X] t D}
    (h : ReturnFragmentWithRules pe computedCalls productReturns ht) : Generated S (ofRegion S (returnRegion_typed ht)) :=
  PairReturnFragment.generated_returnFragment pe S includeJoin calls products h

/-- A contextual seed with the ordered-pair rules generates the fragment.
The computed-call constructor uses the exact call equation when enabled. -/
theorem generated_returnFragment_of
    (S : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
    (includeJoin : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}, Seed Γ r s L → S Γ r s L)
    {computedCalls : Bool} (calls : computedCalls = true → CallReturnAgreement S)
    {X D : τ} {t : Tm Φ} {ht : Tm.HasType [X] t D}
    (h : ReturnFragmentWithCalls pe computedCalls ht) : Generated S (ofRegion S (returnRegion_typed ht)) :=
  generated_returnFragment_with_rules pe S includeJoin calls (productReturns := false) (fun enabled => nomatch enabled) h

/-- Recursive singleton returns in the fragment denote generated arrows in the
pair-return join. -/
theorem generated_returnFragment {X D : τ} {t : Tm Φ} {ht : Tm.HasType [X] t D}
    (h : ReturnFragment pe ht) : Generated Seed (ofRegion Seed (returnRegion_typed ht)) :=
  generated_returnFragment_of pe Seed (fun step => step) (computedCalls := false) (fun enabled => nomatch enabled) h

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns
