module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Singleton.Generation.Defs

/-! # Induction in both directions of the raw generation comparison -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.NormalizedRawGeneration

open Silmaril CategoryTheory
open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Singleton
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Singleton.Generation (Generated)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (S : NormalizedSeed τ Φ)

local notation "Join" => S.step
local notation "H" => RawHom S
local notation "G" => Paper.Extension.Singleton.ofType (Φ := Φ) Join
local notation "GuardedGenerated" => Paper.Extension.Singleton.Generation.Generated Join

local notation "E" => homEquiv S

theorem normalize_generated {A B : τ} {f : H A B} (hf : Generated S f) :
    GuardedGenerated (normalizeHom S f) := by
  induction hf with
  | id A => rw [normalize_identity S]; exact .id A
  | comp _ _ ihf ihg => rw [normalize_compose S]; exact .comp ihf ihg
  | inv i _ ih => exact .inv ((normalizeFunctor S).mapIso i) ih
  | discard A => rw [normalize_discard S]; exact .discard A
  | fst A B => rw [normalize_productFst S]; exact .fst A B
  | snd A B => rw [normalize_productSnd S]; exact .snd A B
  | copy A => rw [normalize_diagonal S]; exact .copy A
  | primitive p => rw [normalize_primitive S]; exact .primitive p
  | initial f => exact .initial _
  | inl A B => rw [normalize_sumInl S]; exact .inl A B
  | inr A B => rw [normalize_sumInr S]; exact .inr A B
  | copair _ _ ihf ihg => rw [normalize_exactCopair S]; exact .copair ihf ihg
  | left X _ ih => rw [normalize_whiskerLeft S]; exact .left X ih
  | right X _ ih => rw [normalize_whiskerRight S]; exact .right X ih
  | iterate _ ih => rw [normalize_iterateSum S]; exact .iterate ih

private theorem toRaw_generated_of_map_eq {A B : τ} {f : H A B} {g : G A ⟶ G B}
    (h : E A B f = g) (hf : Generated S f) : Generated S ((E A B).symm g) :=
  ((E A B).symm_apply_eq.mpr h.symm).symm ▸ hf

theorem toRaw_generated {A B : τ} {g : G A ⟶ G B} (hg : GuardedGenerated g) :
    Generated S ((E A B).symm g) := by
  induction hg with
  | id A => exact toRaw_generated_of_map_eq S (normalize_identity S (A := A)) (.id A)
  | @comp A B D f g _ _ ihf ihg =>
    refine toRaw_generated_of_map_eq S ?_ (.comp ihf ihg)
    exact (normalize_compose S _ _).trans (congrArg₂ _ ((E _ _).apply_symm_apply _) ((E _ _).apply_symm_apply _))
  | inv i _ ih => exact .inv ((toRawFunctor S).mapIso i) ih
  | discard A => exact toRaw_generated_of_map_eq S (normalize_discard S A) (.discard A)
  | fst A B => exact toRaw_generated_of_map_eq S (normalize_productFst S A B) (.fst A B)
  | snd A B => exact toRaw_generated_of_map_eq S (normalize_productSnd S A B) (.snd A B)
  | copy A => exact toRaw_generated_of_map_eq S (normalize_diagonal S A) (.copy A)
  | primitive p => exact toRaw_generated_of_map_eq S (normalize_primitive S p) (.primitive p)
  | initial f => exact .initial _
  | inl A B => exact toRaw_generated_of_map_eq S (normalize_sumInl S A B) (.inl A B)
  | inr A B => exact toRaw_generated_of_map_eq S (normalize_sumInr S A B) (.inr A B)
  | copair _ _ ihf ihg =>
    refine toRaw_generated_of_map_eq S ?_ (.copair ihf ihg)
    exact (normalize_exactCopair S _ _).trans (congrArg₂ _ ((E _ _).apply_symm_apply _) ((E _ _).apply_symm_apply _))
  | @left X A B f _ ih =>
    exact toRaw_generated_of_map_eq S
      ((normalize_whiskerLeft S X ((E A B).symm f)).trans
        (congrArg (Paper.Extension.Singleton.whiskerLeft Join (G X)) ((E A B).apply_symm_apply f)))
      (.left X ih)
  | @right X A B f _ ih =>
    exact toRaw_generated_of_map_eq S
      ((normalize_whiskerRight S X ((E A B).symm f)).trans
        (congrArg (Paper.Extension.Singleton.whiskerRight Join · (G X)) ((E A B).apply_symm_apply f)))
      (.right X ih)
  | iterate _ ih =>
    refine toRaw_generated_of_map_eq S ?_ (.iterate ih)
    exact (normalize_iterateSum S _).trans (congrArg _ ((E _ _).apply_symm_apply _))

theorem generated_iff_normalize {A B : τ} (f : H A B) :
    Generated S f ↔ GuardedGenerated (normalizeHom S f) := by
  refine ⟨normalize_generated S, fun h => ?_⟩
  exact (E A B).symm_apply_apply f ▸ toRaw_generated S h

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.NormalizedRawGeneration
