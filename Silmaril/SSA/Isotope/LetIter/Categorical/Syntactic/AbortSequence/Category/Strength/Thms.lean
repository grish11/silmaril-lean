module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Distributivity.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Iteration.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.CategoryStrength

/-! # The iteration strength law for the LetIter computation quotient -/

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Thesis.LambdaIter.Syn (SynCat)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
variable (pe : ε)

local notation "S" => signature (τ := τ) (Φ := Φ) pe
local notation "Q" => RepairedSynCat (τ := τ) (Φ := Φ) pe
local notation "P" => repairedProjection (τ := τ) (Φ := Φ) pe
local notation "cmp" => repairedProjectionCoprodIso pe

local notation "leftInv" => DistributivePremonoidalCategory.leftInv

/-- Projection commutes with the inverse left distributor after comparing coproducts. -/
theorem repairedProjection_leftInv (X Y Z : SynCat S) :
    (P).obj X ◁ (cmp Y Z).hom ≫ leftInv ((P).obj X) ((P).obj Y) ((P).obj Z) =
      (P).map (leftInv X Y Z) ≫ (cmp (X ⊗ Y) (X ⊗ Z)).hom :=
  RepairedStrengthProofs.repairedProjection_leftInv pe X Y Z

/-- The quotient iteration commutes with threading a fixed context through the loop body. -/
theorem repairedIteration_strength {X Y : Q} (Z : Q) (f : X ⟶ Y ⨿ X) :
    CategoryTheory.iterate ((Z ◁ f) ≫ leftInv Z Y X) = Z ◁ CategoryTheory.iterate f :=
  RepairedStrengthProofs.repairedIteration_strength pe Z f

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
