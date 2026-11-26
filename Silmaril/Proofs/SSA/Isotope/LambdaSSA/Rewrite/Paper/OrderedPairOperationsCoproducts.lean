module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Operations.Thms

/-! # The raw case and empty decoder exhibit the exact finite coproduct structure -/

public section

universe u v w

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairOperationsCoproducts

open Silmaril CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open Paper.Extension.Singleton (ofType ofRegion)

open Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Operations

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "Join" => WithPairReturns.JoinedStep (τ := τ) (Φ := Φ) pe
local notation "Raw" => RawTypeCategory (τ := τ) Φ pe
local notation "G" => ofType (Φ := Φ) Join

set_option backward.isDefEq.respectTransparency false in
noncomputable def sumCofanIsColimit (A B : τ) : IsColimit (sumCofan (Φ := Φ) pe A B) := by
  refine BinaryCofan.IsColimit.mk _ (fun f g => exactCopair pe f g) ?_ ?_ ?_
  · intro Z f g
    apply normalizeHom_injective pe
    change normalizeHom pe (compose pe (sumInl pe A B) (exactCopair pe f g)) = normalizeHom pe f
    rw [normalize_compose, normalize_sumInl, normalize_exactCopair]
    exact (Extension.Singleton.sumCofanIsColimit Join A B).fac
      (BinaryCofan.mk (normalizeHom pe f) (normalizeHom pe g)) ⟨WalkingPair.left⟩
  · intro Z f g
    apply normalizeHom_injective pe
    change normalizeHom pe (compose pe (sumInr pe A B) (exactCopair pe f g)) = normalizeHom pe g
    rw [normalize_compose, normalize_sumInr, normalize_exactCopair]
    exact (Extension.Singleton.sumCofanIsColimit Join A B).fac
      (BinaryCofan.mk (normalizeHom pe f) (normalizeHom pe g)) ⟨WalkingPair.right⟩
  · intro Z f g m hl hr
    apply normalizeHom_injective pe
    have hl' := congrArg (normalizeHom pe) hl
    have hr' := congrArg (normalizeHom pe) hr
    change normalizeHom pe (compose pe (sumInl pe A B) m) = normalizeHom pe f at hl'
    change normalizeHom pe (compose pe (sumInr pe A B) m) = normalizeHom pe g at hr'
    rw [normalize_compose, normalize_sumInl] at hl'
    rw [normalize_compose, normalize_sumInr] at hr'
    change normalizeHom pe m = normalizeHom pe (exactCopair pe f g)
    rw [normalize_exactCopair]
    exact (Extension.Singleton.sumCofanIsColimit Join A B).uniq
      (BinaryCofan.mk (normalizeHom pe f) (normalizeHom pe g))
      (normalizeHom (τ := τ) (Φ := Φ) pe (A := coprod A B) (B := Z.as) m)
      (fun j => by cases j with | mk j => cases j <;> assumption)

noncomputable def emptyIsInitial : IsInitial (⟨Silmaril.empty⟩ : Raw) :=
  IsInitial.ofUniqueHom (fun Y => fromEmpty pe Y.as) (fun _ _ =>
    normalizeHom_injective pe ((Extension.Singleton.emptyIsInitial Join).hom_ext _ _))
theorem sumCofan_desc {A B : τ} {Z : Raw} (f : (⟨A⟩ : Raw) ⟶ Z) (g : (⟨B⟩ : Raw) ⟶ Z) :
    (sumCofanIsColimit pe A B).desc (BinaryCofan.mk f g) = exactCopair pe f g :=
  by rfl

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairOperationsCoproducts
