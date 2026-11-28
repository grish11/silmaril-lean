module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.StructuralValues.Thms

/-! # The exact three-copy uniformity seed over BinaryFold -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling

open Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
  (ofType ofRegion projection iterateChosen homRel)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.StructuralValues (inclusion)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "S" => JoinedStep (τ := τ) (Φ := Φ) pe
local infixr:65 " ⊕ₜ " => Silmaril.coprod

/-- One extra family: the feedback comparison for the exact three-copy
schedule of an arbitrary retained round. Its commuting square is already
proved in BinaryFold. Both representatives have the same exact interface. -/
inductive TriplingStep : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop where
  | uniform {A B : τ} (g : ofType S A ⟶ ofType S B ⨿ ofType S A)
      {r s : Region Φ} (hr : ValueBranches [A ⊕ₜ (A ⊕ₜ A)] r [B])
      (hs : ValueBranches [A ⊕ₜ (A ⊕ₜ A)] s [B])
      (left : ofRegion S hr = iterateChosen S (ternaryStep pe g))
      (right : ofRegion S hs = (inclusion S).map (ternaryFold pe A) ≫ iterateChosen S g) :
      TriplingStep [A ⊕ₜ (A ⊕ₜ A)] r s [B]

/-- Extend the existing BinaryFold seed by this one feedback comparison. -/
abbrev Step (Γ : VCtx τ) (r s : Region Φ) (L : LCtx τ) : Prop :=
  S Γ r s L ∨ TriplingStep pe Γ r s L

abbrev Eqv := Paper.Extension.Eqv (Step (τ := τ) (Φ := Φ) pe)

abbrev TypeCategory := Paper.Extension.Singleton.TypeCategory (Step (τ := τ) (Φ := Φ) pe)

set_option hygiene false in
local notation "T" => Step (τ := τ) (Φ := Φ) pe

/-- The projection is the identity on syntax types and includes every old
BinaryFold derivation into the new contextual quotient. -/
def fromBinaryFold :
    BinaryFold.TypeCategory (τ := τ) (Φ := Φ) pe ⥤ TypeCategory (τ := τ) (Φ := Φ) pe := by
  refine CategoryTheory.Quotient.lift (homRel S) (Paper.Extension.Singleton.projection T) ?_
  intro _ _ _ _ h
  obtain ⟨r, s, hr, hs, hf, hg, eqv⟩ := h
  exact CategoryTheory.Quotient.sound _ ⟨r, s, hr, hs, hf, hg, eqv.mapSeed Or.inl⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling
