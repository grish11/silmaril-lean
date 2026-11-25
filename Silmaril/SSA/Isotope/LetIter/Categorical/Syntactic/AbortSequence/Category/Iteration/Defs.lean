module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Coproducts.Thms

/-! # Iteration in the abort-extended LetIter computation category -/

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open CategoryTheory CategoryTheory.Limits
open Silmaril.Thesis.LambdaIter.Syn (SynCat)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]

variable (pe : ε)

local notation "S" => signature (τ := τ) (Φ := Φ) pe
local notation "P" => repairedProjection (τ := τ) (Φ := Φ) pe

/-- Iterate in the quotient by carrying the body back along the coproduct comparison,
then projecting the iteration of a representative. -/
noncomputable instance repairedIteration : Iteration (RepairedSynCat (τ := τ) (Φ := Φ) pe) where
  iterate {X Y} f :=
    let body := f ≫ (repairedProjectionCoprodIso pe Y.as X.as).inv
    (P).map (CategoryTheory.iterate ((P).preimage body))

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
