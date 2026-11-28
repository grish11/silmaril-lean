module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Iteration.RequestBlocks.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RequestBlocks

/-! # Splitting two sequential request steps in the ordered-pair singleton quotient

The proof uses a factorization of the inner iteration through the original
return-or-repeat sum. Repaired LetIter pure uniformity accepts a square modulo
`AbortEquiv`. Replaying such a square on fixed standard Paper representatives
would require equality before projecting to the joined quotient. The public
`StructuralValues.Uniformity.projected_native_square` and `native_square_ne`
give a square that commutes after projection and fails on those representatives.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns

open Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton (iterateChosen)

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "Seed" => JoinedStep (τ := τ) (Φ := Φ) pe

variable {S R B : Extension.Singleton.TypeCategory (JoinedStep (τ := τ) (Φ := Φ) pe)}

/-- Splitting a two-step row into an original state and a pending reply
preserves guarded iteration from the original-state summand. -/
theorem iterateChosen_requestBlocks (first : S ⟶ R) (second : R ⟶ B ⨿ S) :
    iterateChosen Seed (first ≫ second) =
      coprod.inl ≫ iterateChosen Seed
        (requestBlocks pe first second ≫ (coprod.associator B S R).hom) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RequestBlocks.iterateChosen_requestBlocks pe first second

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns
