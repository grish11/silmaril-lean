module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Defs

/-! # Equality in the abort-extended LetIter computation category -/

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open CategoryTheory
open Silmaril.Thesis.LambdaIter.Syn (SynCat)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]

/-- The computation quotient identifies precisely the repaired hom classes. -/
theorem repairedProjection_map_eq_iff (pe : ε)
    {X Y : SynCat (signature (τ := τ) (Φ := Φ) pe)} (f g : X ⟶ Y) :
    (repairedProjection pe).map f = (repairedProjection pe).map g ↔
      repairedHomClass pe f = repairedHomClass pe g :=
  CategoryTheory.Quotient.functor_map_eq_iff (repairedHomRel pe) f g

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
