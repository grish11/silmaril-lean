module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Generation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Generation.Thms

/-! # Generation of recursive singleton returns -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PairReturnFragment

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithPairReturns
open Paper.Extension.Singleton (ofRegion ofRegion_eq_iff productFst productSnd)
open Paper.Extension.Singleton.Generation (Generated generated_branchValue generated_primitive_branchValue primitive)
open CfgEta.TypeCategory (returnRegion_typed)
open Paper.PackedBody (applyPackedTerm_typed)
open Paper.RetainedLet (unpackBody_typed unpackTerm_typed unpack_return_applyPackedTerm)

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

variable (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
  (includeJoin : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}, JoinedStep pe Γ r s L → Seed Γ r s L)

include includeJoin

theorem returnFst_eq_productFst (A B : τ) :
    ofRegion Seed (returnRegion_typed (Paper.WithProjectionReturns.fstTerm A B)) = productFst Seed A B := by
  apply (ofRegion_eq_iff Seed _ _).2
  exact .extra (Paper.WithProjectionReturns.Step.fst A B).valueBranches.1.hasType
    (Paper.WithProjectionReturns.Step.fst A B).valueBranches.2.hasType
    (includeJoin (.inl (.inl (.inl (.fst A B)))))

theorem returnSnd_eq_productSnd (A B : τ) :
    ofRegion Seed (returnRegion_typed (Paper.WithProjectionReturns.sndTerm A B)) = productSnd Seed A B := by
  apply (ofRegion_eq_iff Seed _ _).2
  exact .extra (Paper.WithProjectionReturns.Step.snd A B).valueBranches.1.hasType
    (Paper.WithProjectionReturns.Step.snd A B).valueBranches.2.hasType
    (includeJoin (.inl (.inl (.inl (.snd A B)))))

set_option backward.isDefEq.respectTransparency false in
theorem generated_returnFragment {computedCalls productReturns : Bool}
    (calls : computedCalls = true → CallReturnAgreement Seed)
    (products : productReturns = true → ProductReturnAgreement Seed)
    {X D : τ} {t : Tm Φ} {ht : Tm.HasType [X] t D}
    (h : ReturnFragmentWithRules pe computedCalls productReturns ht) : Generated Seed (ofRegion Seed (returnRegion_typed ht)) := by
  induction h with
  | value ha =>
    have eq := (ofRegion_eq_iff Seed (returnRegion_typed ha.hasType) (.br (ℓ := 0) rfl ha)).2
      (.paper (.cfgEta (.native (.base (CfgEta.TypeCategory.returnRegion_branchValue ha)))))
    exact eq.symm ▸ generated_branchValue Seed ha
  | primitive p ha => exact generated_primitive_branchValue Seed p ha
  | @call X a p ha enabled _ ga =>
    have inner : Tm.HasType [instrSrc (τ := τ) p] (.op p (.var 0)) (instrTrg p) := .op (.var rfl)
    have comparison :=
      (ofRegion_eq_iff Seed (returnRegion_typed (.op ha))
        (returnRegion_typed (.let₁ ha (inner.rename ((Ren.wk [] X).lift (instrSrc p)))))).2
          (calls enabled p ha)
    rw [comparison, Paper.WithCaseAndUnaryReturns.returnLet_eq_comp Seed ha inner]
    exact .comp ga (.primitive p)
  | @seq X A D a b ha hb _ _ ga gb =>
    rw [Paper.WithCaseAndUnaryReturns.returnLet_eq_comp Seed ha hb]
    exact .comp ga gb
  | @retained X A D a c ha hc _ _ ga gc =>
    exact Paper.RetainedLet.generated_packed_returnLet Seed pe
      (fun step => includeJoin (.inl (.inr step))) ha hc ga gc
  | @destructure X A D c hc enabled _ gc =>
    let body := applyPackedTerm_typed hc
    have eq := (ofRegion_eq_iff Seed (unpackBody_typed (returnRegion_typed body))
      (returnRegion_typed (unpackTerm_typed body))).2 (products enabled body)
    have packed := unpack_return_applyPackedTerm Seed (fun step => includeJoin (.inl (.inr (.inl step)))) hc
    exact (packed.symm.trans eq) ▸ gc
  | @caseInput A B D a b ha hb pa pb _ _ ga gb =>
    rw [Paper.WithCaseAndUnaryReturns.returnCase_eq_copair pe Seed (fun step => includeJoin (.inl (.inr step))) ha hb pa pb]
    exact .copair ga gb
  | @pair X A B a b ha hb _ _ ga gb =>
    exact generated_returnPair Seed (fun step => includeJoin (.inr step)) (fun step => includeJoin (.inl (.inr (.inl step)))) ha hb ga gb
  | fst A B =>
    rw [returnFst_eq_productFst pe Seed includeJoin A B]
    exact .fst A B
  | snd A B =>
    rw [returnSnd_eq_productSnd pe Seed includeJoin A B]
    exact .snd A B

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PairReturnFragment
