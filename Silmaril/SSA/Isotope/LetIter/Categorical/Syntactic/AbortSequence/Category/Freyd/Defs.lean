module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Tensor.Thms

/-! # Projected braiding for the LetIter computation quotient -/

@[expose] public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open CategoryTheory
open scoped MonoidalCategory

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
variable (pe : ε)

local notation "Q" => RepairedSynCat (τ := τ) (Φ := Φ) pe
local notation "P" => repairedProjection (τ := τ) (Φ := Φ) pe

/-- The braiding of the repaired computation tensor is the projection of the exact braiding. -/
def repairedBraiding (X Y : Q) : X ⊗ Y ≅ Y ⊗ X :=
  (P).mapIso (BraidedPremonoidalCategory.braiding X.as Y.as)

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
