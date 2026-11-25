module

public import Silmaril.SSA.Thesis.SyntacticCategory.Tensor.Iteration.Thms
import Silmaril.Proofs.SSA.Thesis.SyntacticCategory.Tensor.Strength

/-! # Strong Elgot iteration in the exact λiter syntactic Freyd category -/

public section

universe u

namespace Silmaril.Thesis.LambdaIter.Syn.SynCat

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

variable {S : Sig.{u}}

/-- Threading a fixed value through every step of a loop agrees with tensoring
that value with the result of iteration. The loop body can be effectful. -/
theorem iterate'_strength (R : SynCat S) {X Y : SynCat S} (f : X ⟶ Y ⨿ X) :
    iterate' ((R ◁ f) ≫ DistributivePremonoidalCategory.leftInv R Y X) =
      R ◁ iterate' f :=
  iterate'_strength_proof R f

/-- The exact syntactic value inclusion carries strong Elgot iteration. -/
noncomputable instance valuesStrongElgotFreyd (S : Sig.{u}) : StrongElgotFreydCategory (values S) where
  iterate_whiskerLeft R f := iterate'_strength R f

end Silmaril.Thesis.LambdaIter.Syn.SynCat
