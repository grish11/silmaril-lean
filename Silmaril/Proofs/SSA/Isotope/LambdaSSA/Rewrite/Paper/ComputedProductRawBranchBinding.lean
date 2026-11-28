module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.BranchBinding.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProductDestructureReturns.BranchBinding.Thms

/-! # Replay the literal producer under typed branch binding -/

public section

universe u v w

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComputedProductRawBranchBinding

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open Paper.WithComputedProductProducers
open Paper.WithComputedProductProducers.BranchBinding (RawStep RawJoinedStep)
open Paper.SingletonReification.BinaryLet (returnPair returnPair_typed)
open Paper.RetainedLet (returnOnce returnOnce_typed)
open Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding
  (AddBinding ofSeed eqv_iff_normalized_of_guardedSeed)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)
  {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}

private theorem bind_exit {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
    {X A : τ} {a : Tm Φ} (ha : Tm.HasType [X] a A) :
    Extension.Eqv (AddBinding Seed) [X] (.br 0 a) (returnOnce a) [A] :=
  .extra (.br rfl ha) (returnOnce_typed ha).hasType (.inr (.bind rfl ha))

private theorem raw_seed_eqv {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}
    (h : RawStep Γ r s L) :
    Extension.Eqv (AddBinding (JoinedStep pe)) Γ r s L := by
  cases h with
  | producer ha => exact (ofSeed (productProducerAgreement pe ha)).trans (bind_exit ha).symm

private theorem guarded_seed_eqv (h : Step Γ r s L) :
    Extension.Eqv (RawJoinedStep pe) Γ r s L := by
  cases h with
  | producer ha => exact (Extension.Eqv.extra (returnPair_typed ha).hasType (.br rfl ha)
      (.inl (.inr (.producer ha)))).trans (bind_exit ha)

private theorem replaySeed
    {Source Target : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
    (map : ∀ {Γ r s L}, HasType Γ r L → HasType Γ s L → Source Γ r s L → Extension.Eqv Target Γ r s L)
    (h : Extension.Eqv Source Γ r s L) : Extension.Eqv Target Γ r s L := by
  induction h with
  | paper h => exact .paper h
  | extra hr hs e => exact map hr hs e
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ ihl ihr => exact .case ha ihl ihr
  | cfg R _ _ ihe ihb => exact .cfg R ihe ihb
  | lsubstCongr hp _ ih => exact .lsubstCongr hp ih
  | lsubstPost _ hr hs hσ ih => exact .lsubstPost ih hr hs hσ
  | substVars _ hθ ih => exact .substVars ih hθ
  | renameLabels _ hρ ih => exact .renameLabels ih hρ

theorem raw_eqv_iff_replayed :
    Extension.Eqv (RawJoinedStep pe) Γ r s L ↔
      Extension.Eqv (AddBinding (JoinedStep pe)) Γ r s L :=
  ⟨replaySeed (fun hr hs e =>
      e.elim (fun e => e.elim (fun e => .extra hr hs (.inl (.inl e))) (raw_seed_eqv pe))
        (fun e => .extra hr hs (.inr e))),
    replaySeed (fun hr hs e =>
      e.elim (fun e => e.elim (fun e => .extra hr hs (.inl (.inl e))) (guarded_seed_eqv pe))
        (fun e => .extra hr hs (.inr e)))⟩

theorem raw_eqv_iff_normalized (hr : HasType Γ r L) (hs : HasType Γ s L) :
    Extension.Eqv (RawJoinedStep pe) Γ r s L ↔
      Extension.Eqv (JoinedStep pe) Γ r.bindBranchArguments s.bindBranchArguments L :=
  (raw_eqv_iff_replayed pe).trans (eqv_iff_normalized_of_guardedSeed
    (fun h => h.elim WithProductDestructureReturns.joined_valueBranches Step.valueBranches) hr hs)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComputedProductRawBranchBinding
