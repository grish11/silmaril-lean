module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Operations.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Generation.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairOperations

/-! # Raw fixed-factor actions and the exact copair commute with normalization -/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Operations

open Silmaril CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton (ofType ofRegion)

open CfgEta.TypeCategory (productFstBranches productSndBranches)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "Join" => WithPairReturns.JoinedStep (τ := τ) (Φ := Φ) pe
local notation "G" => ofType (Φ := Φ) Join
local notation "H" => RawHom (Φ := Φ) pe

variable {A B D : τ}

section

variable (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

theorem ofRegion_bind_whiskerLeftRep (X : τ) (r : Rep (Φ := Φ) A B) :
    ofRegion Seed (whiskerLeftRep X r).property.bindBranchArguments =
      Extension.Singleton.whiskerLeft Seed (ofType Seed X) (ofRegion Seed r.property.bindBranchArguments) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairOperations.ofRegion_bind_whiskerLeftRep Seed X r

theorem ofRegion_bind_whiskerRightRep (X : τ) (r : Rep (Φ := Φ) A B) :
    ofRegion Seed (whiskerRightRep X r).property.bindBranchArguments =
      Extension.Singleton.whiskerRight Seed (ofRegion Seed r.property.bindBranchArguments) (ofType Seed X) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairOperations.ofRegion_bind_whiskerRightRep Seed X r

theorem ofRegion_bind_copairRep (r : Rep (Φ := Φ) A D) (s : Rep (Φ := Φ) B D) :
    ofRegion Seed (copairRep r s).property.bindBranchArguments =
      Extension.Singleton.ValueCoproducts.exactCopair Seed
        (ofRegion Seed r.property.bindBranchArguments) (ofRegion Seed s.property.bindBranchArguments) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairOperations.ofRegion_bind_copairRep Seed r s

end

theorem normalize_whiskerLeftRep (X : τ) (r : Rep (Φ := Φ) A B) :
    normalizeHom pe (Quotient.mk _ (whiskerLeftRep X r)) =
      Extension.Singleton.whiskerLeft Join (G X) (normalizeHom pe (Quotient.mk _ r)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairOperations.normalize_whiskerLeftRep pe X r

theorem normalize_whiskerRightRep (X : τ) (r : Rep (Φ := Φ) A B) :
    normalizeHom pe (Quotient.mk _ (whiskerRightRep X r)) =
      Extension.Singleton.whiskerRight Join (normalizeHom pe (Quotient.mk _ r)) (G X) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairOperations.normalize_whiskerRightRep pe X r

theorem normalize_copairRep (r : Rep (Φ := Φ) A D) (s : Rep (Φ := Φ) B D) :
    normalizeHom pe (Quotient.mk _ (copairRep r s)) =
      Extension.Singleton.ValueCoproducts.exactCopair Join
        (normalizeHom pe (Quotient.mk _ r)) (normalizeHom pe (Quotient.mk _ s)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairOperations.normalize_copairRep pe r s

/-- Apply the literal bound right computation while retaining the left factor. -/
def whiskerLeft (X : τ) (f : H A B) : H (product X A) (product X B) :=
  Quotient.map (whiskerLeftRep X) (fun r s h => Quotient.exact
    (normalizeHom_injective pe (by
      rw [normalize_whiskerLeftRep, normalize_whiskerLeftRep,
        congrArg (normalizeHom pe) (Quotient.sound h)]))) f

/-- Apply the literal bound left computation while retaining the right factor. -/
def whiskerRight (X : τ) (f : H A B) : H (product A X) (product B X) :=
  Quotient.map (whiskerRightRep X) (fun r s h => Quotient.exact
    (normalizeHom_injective pe (by
      rw [normalize_whiskerRightRep, normalize_whiskerRightRep,
        congrArg (normalizeHom pe) (Quotient.sound h)]))) f

/-- Copair the raw arrows by the literal case on their exact syntax sum. -/
def exactCopair (f : H A D) (g : H B D) : H (coprod A B) D :=
  Quotient.map₂ copairRep (fun r r' hr s s' hs => Quotient.exact
    (normalizeHom_injective pe (by
      rw [normalize_copairRep, normalize_copairRep, congrArg (normalizeHom pe) (Quotient.sound hr),
        congrArg (normalizeHom pe) (Quotient.sound hs)]))) f g

theorem normalize_whiskerLeft (X : τ) (f : H A B) :
    normalizeHom pe (whiskerLeft pe X f) = Extension.Singleton.whiskerLeft Join (G X) (normalizeHom pe f) :=
  Quotient.inductionOn f (normalize_whiskerLeftRep pe X)

theorem normalize_whiskerRight (X : τ) (f : H A B) :
    normalizeHom pe (whiskerRight pe X f) = Extension.Singleton.whiskerRight Join (normalizeHom pe f) (G X) :=
  Quotient.inductionOn f (normalize_whiskerRightRep pe X)

theorem normalize_exactCopair (f : H A D) (g : H B D) :
    normalizeHom pe (exactCopair pe f g) =
      Extension.Singleton.ValueCoproducts.exactCopair Join (normalizeHom pe f) (normalizeHom pe g) :=
  Quotient.inductionOn₂ f g (normalize_copairRep pe)

theorem normalize_primitive (p : Φ) :
    normalizeHom pe (primitive (τ := τ) pe p) = Extension.Singleton.Generation.primitive Join p :=
  rfl

theorem normalize_discard (A : τ) :
    normalizeHom pe (discard pe A) = Extension.Singleton.discardArrow Join A :=
  normalize_guarded pe (.br (ℓ := 0) rfl .unit)

theorem normalize_diagonal (A : τ) :
    normalizeHom pe (diagonal pe A) = Extension.Singleton.diagonalArrow Join (G A) :=
  normalize_guarded pe (Paper.RetainedLet.diagonal_typed A)

theorem normalize_productFst (A B : τ) :
    normalizeHom pe (productFst pe A B) = Extension.Singleton.productFst Join A B :=
  normalize_guarded pe (productFstBranches A B)

theorem normalize_productSnd (A B : τ) :
    normalizeHom pe (productSnd pe A B) = Extension.Singleton.productSnd Join A B :=
  normalize_guarded pe (productSndBranches A B)

theorem normalize_sumInl (A B : τ) :
    normalizeHom pe (sumInl pe A B) = (Extension.Singleton.sumCofan Join A B).inl := by
  change _ = (Extension.Singleton.projection Join).map (Paper.TypeCategory.sumCofan A B).inl
  rw [Paper.TypeCategory.sumCofan_inl]
  exact normalize_guarded pe (.br (ℓ := 0) rfl (.inl (.var (i := 0) rfl)))

theorem normalize_sumInr (A B : τ) :
    normalizeHom pe (sumInr pe A B) = (Extension.Singleton.sumCofan Join A B).inr := by
  change _ = (Extension.Singleton.projection Join).map (Paper.TypeCategory.sumCofan A B).inr
  rw [Paper.TypeCategory.sumCofan_inr]
  exact normalize_guarded pe (.br (ℓ := 0) rfl (.inr (.var (i := 0) rfl)))

theorem normalize_fromEmpty (A : τ) :
    normalizeHom pe (fromEmpty pe A) = (Extension.Singleton.emptyIsInitial Join).to (G A) :=
  (Extension.Singleton.emptyIsInitial Join).hom_ext _ _

theorem normalize_braid (A B : τ) :
    normalizeHom pe (braid pe A B) = (Extension.Singleton.braidIso Join (G A) (G B)).hom :=
  normalize_guarded pe (Paper.TypeCategory.braidBranches A B)

theorem normalize_associate (A B C : τ) :
    normalizeHom pe (associate pe A B C) = (Extension.Singleton.associateIso Join (G A) (G B) (G C)).hom :=
  normalize_guarded pe (Paper.TypeCategory.associate_typed A B C)

theorem normalize_unassociate (A B C : τ) :
    normalizeHom pe (unassociate pe A B C) = (Extension.Singleton.associateIso Join (G A) (G B) (G C)).inv :=
  normalize_guarded pe (Paper.TypeCategory.unassociate_typed A B C)

theorem normalize_leftUnitSection (A : τ) :
    normalizeHom pe (leftUnitSection pe A) =
      (Extension.Singleton.projection Join).map (Paper.TypeCategory.leftUnitSection A) :=
  normalize_guarded pe (.br (ℓ := 0) rfl (.pair .unit (.var (i := 0) rfl)))

theorem normalize_rightUnitSection (A : τ) :
    normalizeHom pe (rightUnitSection pe A) =
      (Extension.Singleton.projection Join).map (Paper.TypeCategory.rightUnitSection A) :=
  normalize_guarded pe (.br (ℓ := 0) rfl (.pair (.var (i := 0) rfl) .unit))

theorem normalize_unitProjectionLeft (A : τ) :
    normalizeHom pe (productSnd pe Silmaril.unit A) = Extension.Singleton.unitProjectionLeft Join (G A) :=
  normalize_productSnd pe Silmaril.unit A

theorem normalize_unitProjectionRight (A : τ) :
    normalizeHom pe (productFst pe A Silmaril.unit) = Extension.Singleton.unitProjectionRight Join (G A) :=
  normalize_productFst pe A Silmaril.unit

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Operations
