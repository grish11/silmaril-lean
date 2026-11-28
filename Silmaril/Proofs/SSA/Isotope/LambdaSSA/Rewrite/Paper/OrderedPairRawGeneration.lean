module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Generation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Operations.Comparison.Thms

/-! # Induction in both directions of the raw generation comparison -/

public section

universe u v w

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairRawGeneration

open Silmaril CategoryTheory
open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Generation (Generated)
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Operations (operationIso)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "Join" => WithPairReturns.JoinedStep (τ := τ) (Φ := Φ) pe
local notation "H" => RawHom (Φ := Φ) pe
local notation "G" => Paper.Extension.Singleton.ofType (Φ := Φ) Join
local notation "GuardedGenerated" => Paper.Extension.Singleton.Generation.Generated Join

local notation "Cmp" => operationIso (τ := τ) (Φ := Φ) pe
local notation "E" => Operations.OperationIso.homEquiv (Cmp)

theorem normalize_generated {A B : τ} {f : H A B} (hf : Generated pe f) :
    GuardedGenerated (E A B f) := by
  induction hf with
  | id A => rw [(Cmp).map_id]; exact .id A
  | comp _ _ ihf ihg => rw [(Cmp).map_comp]; exact .comp ihf ihg
  | inv i _ ih => exact .inv ((normalizeFunctor pe).mapIso i) ih
  | discard A => rw [(Cmp).map_discard]; exact .discard A
  | fst A B => rw [(Cmp).map_productFst]; exact .fst A B
  | snd A B => rw [(Cmp).map_productSnd]; exact .snd A B
  | copy A => rw [(Cmp).map_diagonal]; exact .copy A
  | primitive p => rw [(Cmp).map_primitive]; exact .primitive p
  | initial f => exact .initial _
  | inl A B => rw [(Cmp).map_sumInl]; exact .inl A B
  | inr A B => rw [(Cmp).map_sumInr]; exact .inr A B
  | copair _ _ ihf ihg => rw [(Cmp).map_exactCopair]; exact .copair ihf ihg
  | left X _ ih => rw [(Cmp).map_whiskerLeft]; exact .left X ih
  | right X _ ih => rw [(Cmp).map_whiskerRight]; exact .right X ih
  | iterate _ ih => rw [(Cmp).map_iterateSum]; exact .iterate ih

private theorem toRaw_generated_of_map_eq {A B : τ} {f : H A B} {g : G A ⟶ G B}
    (h : E A B f = g) (hf : Generated pe f) : Generated pe ((E A B).symm g) :=
  ((E A B).symm_apply_eq.mpr h.symm).symm ▸ hf

theorem toRaw_generated {A B : τ} {g : G A ⟶ G B} (hg : GuardedGenerated g) :
    Generated pe ((E A B).symm g) := by
  induction hg with
  | id A => exact toRaw_generated_of_map_eq pe ((Cmp).map_id A) (.id A)
  | @comp A B D f g _ _ ihf ihg =>
    refine toRaw_generated_of_map_eq pe ?_ (.comp ihf ihg)
    rw [(Cmp).map_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  | inv i _ ih => exact .inv ((toRawFunctor pe).mapIso i) ih
  | discard A => exact toRaw_generated_of_map_eq pe ((Cmp).map_discard A) (.discard A)
  | fst A B => exact toRaw_generated_of_map_eq pe ((Cmp).map_productFst A B) (.fst A B)
  | snd A B => exact toRaw_generated_of_map_eq pe ((Cmp).map_productSnd A B) (.snd A B)
  | copy A => exact toRaw_generated_of_map_eq pe ((Cmp).map_diagonal A) (.copy A)
  | primitive p => exact toRaw_generated_of_map_eq pe ((Cmp).map_primitive p) (.primitive p)
  | initial f => exact .initial _
  | inl A B => exact toRaw_generated_of_map_eq pe ((Cmp).map_sumInl A B) (.inl A B)
  | inr A B => exact toRaw_generated_of_map_eq pe ((Cmp).map_sumInr A B) (.inr A B)
  | copair _ _ ihf ihg =>
    refine toRaw_generated_of_map_eq pe ?_ (.copair ihf ihg)
    rw [(Cmp).map_exactCopair, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  | @left X A B f _ ih =>
    exact toRaw_generated_of_map_eq pe
      (((Cmp).map_whiskerLeft X ((E A B).symm f)).trans
        (congrArg (Paper.Extension.Singleton.whiskerLeft Join (G X)) ((E A B).apply_symm_apply f)))
      (.left X ih)
  | @right X A B f _ ih =>
    exact toRaw_generated_of_map_eq pe
      (((Cmp).map_whiskerRight X ((E A B).symm f)).trans
        (congrArg (Paper.Extension.Singleton.whiskerRight Join · (G X)) ((E A B).apply_symm_apply f)))
      (.right X ih)
  | iterate _ ih =>
    refine toRaw_generated_of_map_eq pe ?_ (.iterate ih)
    rw [(Cmp).map_iterateSum, Equiv.apply_symm_apply]

theorem generated_iff_normalize {A B : τ} (f : H A B) :
    Generated pe f ↔ GuardedGenerated (normalizeHom pe f) := by
  refine ⟨normalize_generated pe, fun h => ?_⟩
  exact (E A B).symm_apply_apply f ▸ toRaw_generated pe h

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairRawGeneration
