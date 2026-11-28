module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Bekic.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonBlocks

/-! # Block elimination at exact sums in default Paper -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] (R P : τ) {Y : τ}
  (r : ofType (Φ := Φ) R ⟶ (ofType Y ⨿ ofType R) ⨿ ofType P)
  (c : ofType (Φ := Φ) P ⟶ (ofType Y ⨿ ofType R) ⨿ ofType P)

/-- Solve the right block first, with the left block among its exits.
Both rows may repeat into either block. The proof uses the fixpoint,
naturality and codiagonal laws and uniformity along the two constructor
injections. -/
theorem iterate_blockStep :
    sumInl R P ≫ iterate (blockStep R P r c) = iterate (r ≫ coprod.desc (𝟙 _) (iterate c)) ∧
    sumInr R P ≫ iterate (blockStep R P r c) =
      iterate c ≫ coprod.desc (𝟙 _) (sumInl R P ≫ iterate (blockStep R P r c)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonBlocks.bekic R P r c

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
