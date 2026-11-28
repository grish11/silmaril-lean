module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.PartialFold

/-! # Uniformity along `id + phaseFold`, derived from the total fold

No seed is added. The state is cut into the exit of the block: the block
alone is a step with exits `Y + A`, and the total-fold seed applies to it.
Block elimination in default Paper then reassembles both entries.

## Premises, both equations of default Paper

* `entry`: the state row followed by the fold of where it enters the block
  is the folded state row.
* `block`: the fold is a simulation of the block onto the folded block,
  with the state among the exits.

## Supported shape

One untouched state, of the same type as the folded phases, whose row
exits or enters the block and does not repeat into itself. The block may
exit, return to the state, or stay in the block.

## A wider shape

`PartialFold.Feedback` covers an untouched block of any type that may
repeat into itself. Block elimination with feedback in the left block
holds in default Paper at exact sums, so no law of the quotient's chosen
coproducts has to be transported.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity

open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory (ofType iterate phaseType phaseFold phaseInl phaseInr joinedStep partialFold)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε) (A : τ) (k : Nat) {Y : τ}
  (a : ofType (Φ := Φ) A ⟶ ofType Y ⨿ ofType (phaseType A k))
  (c : ofType (Φ := Φ) (phaseType A k) ⟶ (ofType Y ⨿ ofType A) ⨿ ofType (phaseType A k))
  (a' : ofType (Φ := Φ) A ⟶ ofType Y ⨿ ofType A)
  (c' : ofType (Φ := Φ) A ⟶ (ofType Y ⨿ ofType A) ⨿ ofType A)
  (entry : a ≫ coprod.map (𝟙 _) (phaseFold A k) = a')
  (block : c ≫ coprod.map (𝟙 _) (phaseFold A k) = phaseFold A k ≫ c')

include entry block in
/-- Entered at the untouched state, the two loops agree. -/
theorem partial_fold_state :
    (projection pe).map (phaseInl A k ≫ iterate (joinedStep A k a c)) =
      (projection pe).map (phaseInl A 0 ≫ iterate (joinedStep A 0 a' c')) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.partial_state pe A k a c a' c' entry block

include entry block in
/-- Entered in the block, the loop is the fold followed by the folded loop. -/
theorem partial_fold_block :
    (projection pe).map (phaseInr A k ≫ iterate (joinedStep A k a c)) =
      (projection pe).map (phaseFold A k ≫ phaseInr A 0 ≫ iterate (joinedStep A 0 a' c')) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.partial_block pe A k a c a' c' entry block

include entry block in
/-- Uniformity along the partial fold for joined steps of this shape. -/
theorem partial_fold :
    (projection pe).map (iterate (joinedStep A k a c)) =
      (projection pe).map (partialFold A k ≫ iterate (joinedStep A 0 a' c')) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.partial_uniform pe A k a c a' c' entry block

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity
