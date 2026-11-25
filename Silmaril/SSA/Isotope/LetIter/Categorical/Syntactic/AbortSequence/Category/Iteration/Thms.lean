module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Iteration.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.CategoryIteration

/-! # Projection and Elgot equations for LetIter quotient iteration -/

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open CategoryTheory CategoryTheory.Limits
open Silmaril.Thesis.LambdaIter.Syn (SynCat)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]

variable (pe : ε)

local notation "S" => signature (τ := τ) (Φ := Φ) pe
local notation "P" => repairedProjection (τ := τ) (Φ := Φ) pe

/-- Iteration commutes with projection after the coproduct comparison. -/
theorem repairedIteration_map {X Y : SynCat S} (f : X ⟶ Y ⨿ X) :
    CategoryTheory.iterate ((P).map f ≫ (repairedProjectionCoprodIso pe Y X).hom) =
      (P).map (CategoryTheory.iterate f) :=
  RepairedIterationProofs.repairedIteration_map pe f

/-- Quotient iteration satisfies the Elgot fixpoint equation. -/
theorem repairedIteration_fixpoint {X Y : RepairedSynCat (τ := τ) (Φ := Φ) pe}
    (f : X ⟶ Y ⨿ X) :
    CategoryTheory.iterate f = f ≫ coprod.desc (𝟙 Y) (CategoryTheory.iterate f) :=
  RepairedIterationProofs.repairedIteration_fixpoint pe f

/-- Quotient iteration satisfies the Elgot naturality equation. -/
theorem repairedIteration_naturality {X Y Z : RepairedSynCat (τ := τ) (Φ := Φ) pe}
    (f : X ⟶ Y ⨿ X) (g : Y ⟶ Z) :
    CategoryTheory.iterate f ≫ g = CategoryTheory.iterate (f ≫ coprod.map g (𝟙 X)) :=
  RepairedIterationProofs.repairedIteration_naturality pe f g

/-- Quotient iteration satisfies the Elgot codiagonal equation. -/
theorem repairedIteration_codiagonal {X Y : RepairedSynCat (τ := τ) (Φ := Φ) pe}
    (f : X ⟶ (Y ⨿ X) ⨿ X) :
    CategoryTheory.iterate (CategoryTheory.iterate f) =
      CategoryTheory.iterate (f ≫ coprod.desc (𝟙 (Y ⨿ X)) (coprod.inr : X ⟶ Y ⨿ X)) :=
  RepairedIterationProofs.repairedIteration_codiagonal pe f

/-- The computation quotient satisfies the three Elgot iteration equations. -/
instance repairedElgotCategory : ElgotCategory (RepairedSynCat (τ := τ) (Φ := Φ) pe) where
  fixpoint f := repairedIteration_fixpoint pe f
  naturality f g := repairedIteration_naturality pe f g
  codiagonal f := repairedIteration_codiagonal pe f

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
