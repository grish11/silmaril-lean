module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Operations.Thms

/-! # Literal raw fixed-factor actions, copair, and structural generators -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Singleton

open CategoryTheory
open Paper.Extension.Singleton (ofType)
open OrderedPairSingleton (Rep)
open OrderedPairSingleton.Operations (whiskerLeftRep whiskerRightRep copairRep)
open CfgEta.TypeCategory (productFstBranches productSndBranches)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] (S : NormalizedSeed τ Φ)
  {A B D : τ}

local notation "G" => ofType S.step
local notation "H" => RawHom S

theorem normalize_whiskerLeftRep (X : τ) (r : Rep (Φ := Φ) A B) :
    normalizeHom S (Quotient.mk _ (whiskerLeftRep X r)) =
      Extension.Singleton.whiskerLeft S.step (G X) (normalizeHom S (Quotient.mk _ r)) :=
  OrderedPairSingleton.Operations.ofRegion_bind_whiskerLeftRep S.step X r

theorem normalize_whiskerRightRep (X : τ) (r : Rep (Φ := Φ) A B) :
    normalizeHom S (Quotient.mk _ (whiskerRightRep X r)) =
      Extension.Singleton.whiskerRight S.step (normalizeHom S (Quotient.mk _ r)) (G X) :=
  OrderedPairSingleton.Operations.ofRegion_bind_whiskerRightRep S.step X r

theorem normalize_copairRep (r : Rep (Φ := Φ) A D) (s : Rep (Φ := Φ) B D) :
    normalizeHom S (Quotient.mk _ (copairRep r s)) =
      Extension.Singleton.ValueCoproducts.exactCopair S.step
        (normalizeHom S (Quotient.mk _ r)) (normalizeHom S (Quotient.mk _ s)) :=
  OrderedPairSingleton.Operations.ofRegion_bind_copairRep S.step r s

/-- Apply the literal bound right computation while retaining the left factor. -/
def whiskerLeft (X : τ) (f : H A B) : H (product X A) (product X B) :=
  Quotient.map (whiskerLeftRep X) (fun r s h => Quotient.exact
    (normalizeHom_injective S (by
      rw [normalize_whiskerLeftRep, normalize_whiskerLeftRep,
        congrArg (normalizeHom S) (Quotient.sound h)]))) f

/-- Apply the literal bound left computation while retaining the right factor. -/
def whiskerRight (X : τ) (f : H A B) : H (product A X) (product B X) :=
  Quotient.map (whiskerRightRep X) (fun r s h => Quotient.exact
    (normalizeHom_injective S (by
      rw [normalize_whiskerRightRep, normalize_whiskerRightRep,
        congrArg (normalizeHom S) (Quotient.sound h)]))) f

/-- Copair the raw arrows by the literal case on their exact syntax sum. -/
def exactCopair (f : H A D) (g : H B D) : H (coprod A B) D :=
  Quotient.map₂ copairRep (fun r r' hr s s' hs => Quotient.exact
    (normalizeHom_injective S (by
      rw [normalize_copairRep, normalize_copairRep, congrArg (normalizeHom S) (Quotient.sound hr),
        congrArg (normalizeHom S) (Quotient.sound hs)]))) f g

theorem normalize_whiskerLeft (X : τ) (f : H A B) :
    normalizeHom S (whiskerLeft S X f) = Extension.Singleton.whiskerLeft S.step (G X) (normalizeHom S f) :=
  Quotient.inductionOn f (normalize_whiskerLeftRep S X)

theorem normalize_whiskerRight (X : τ) (f : H A B) :
    normalizeHom S (whiskerRight S X f) = Extension.Singleton.whiskerRight S.step (normalizeHom S f) (G X) :=
  Quotient.inductionOn f (normalize_whiskerRightRep S X)

theorem normalize_exactCopair (f : H A D) (g : H B D) :
    normalizeHom S (exactCopair S f g) =
      Extension.Singleton.ValueCoproducts.exactCopair S.step (normalizeHom S f) (normalizeHom S g) :=
  Quotient.inductionOn₂ f g (normalize_copairRep S)

def discard (A : τ) : H A Silmaril.unit :=
  rawClass S (.br (ℓ := 0) rfl .unit)

def diagonal (A : τ) : H A (product A A) :=
  rawClass S (.br (ℓ := 0) rfl (.pair (.var (i := 0) rfl) (.var (i := 0) rfl)))

def productFst (A B : τ) : H (product A B) A :=
  rawClass S (productFstBranches A B).hasType

def productSnd (A B : τ) : H (product A B) B :=
  rawClass S (productSndBranches A B).hasType

def sumInl (A B : τ) : H A (coprod A B) :=
  rawClass S (.br (ℓ := 0) rfl (.inl (.var (i := 0) rfl)))

def sumInr (A B : τ) : H B (coprod A B) :=
  rawClass S (.br (ℓ := 0) rfl (.inr (.var (i := 0) rfl)))

theorem normalize_discard (A : τ) :
    normalizeHom S (discard S A) = Extension.Singleton.discardArrow S.step A :=
  normalize_guarded S (.br (ℓ := 0) rfl .unit)

theorem normalize_diagonal (A : τ) :
    normalizeHom S (diagonal S A) = Extension.Singleton.diagonalArrow S.step (G A) :=
  normalize_guarded S (Paper.RetainedLet.diagonal_typed A)

theorem normalize_productFst (A B : τ) :
    normalizeHom S (productFst S A B) = Extension.Singleton.productFst S.step A B :=
  normalize_guarded S (productFstBranches A B)

theorem normalize_productSnd (A B : τ) :
    normalizeHom S (productSnd S A B) = Extension.Singleton.productSnd S.step A B :=
  normalize_guarded S (productSndBranches A B)

theorem normalize_sumInl (A B : τ) :
    normalizeHom S (sumInl S A B) = (Extension.Singleton.sumCofan S.step A B).inl := by
  change _ = (Extension.Singleton.projection S.step).map (Paper.TypeCategory.sumCofan A B).inl
  rw [Paper.TypeCategory.sumCofan_inl]
  exact normalize_guarded S (.br (ℓ := 0) rfl (.inl (.var (i := 0) rfl)))

theorem normalize_sumInr (A B : τ) :
    normalizeHom S (sumInr S A B) = (Extension.Singleton.sumCofan S.step A B).inr := by
  change _ = (Extension.Singleton.projection S.step).map (Paper.TypeCategory.sumCofan A B).inr
  rw [Paper.TypeCategory.sumCofan_inr]
  exact normalize_guarded S (.br (ℓ := 0) rfl (.inr (.var (i := 0) rfl)))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Singleton
