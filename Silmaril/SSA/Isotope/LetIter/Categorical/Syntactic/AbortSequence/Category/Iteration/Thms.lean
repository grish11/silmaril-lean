module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Iteration.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.CategoryIteration

/-! # Projection and fixpoint for LetIter quotient iteration -/

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

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
