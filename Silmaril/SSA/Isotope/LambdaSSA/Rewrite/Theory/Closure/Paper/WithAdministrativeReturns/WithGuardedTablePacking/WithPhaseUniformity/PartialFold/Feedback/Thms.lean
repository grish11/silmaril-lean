module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Projection.Thms

/-! # Uniformity along `id_R + phaseFold` when `R` has its own feedback

No seed is added. `R` is any type. Its row may exit, repeat into `R`, or
enter the block of phases. The block may exit, go to `R`, or stay.

## Premises, both equations of default Paper

* `row`: the row of `R` followed by the fold of where it enters the block
  is the folded row.
* `block`: the fold is a simulation of the block onto the folded block,
  with `R` among the exits.

The seed is used once, on the block alone. Everything else is block
elimination in default Paper and the transport of copairing and iteration
along the projection.

The conclusion is again of the form `inner` of `projection_right_block`,
so the construction nests: a further untouched block may be added on the
left of `R + phases`.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity

open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory (ofType iterate phaseType phaseFold sumInl sumInr blockStep sumMap)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε) (R A : τ) (k : Nat) {Y : τ}
  (r : ofType (Φ := Φ) R ⟶ (ofType Y ⨿ ofType R) ⨿ ofType (phaseType A k))
  (c : ofType (Φ := Φ) (phaseType A k) ⟶ (ofType Y ⨿ ofType R) ⨿ ofType (phaseType A k))
  (r' : ofType (Φ := Φ) R ⟶ (ofType Y ⨿ ofType R) ⨿ ofType A)
  (c' : ofType (Φ := Φ) A ⟶ (ofType Y ⨿ ofType R) ⨿ ofType A)
  (row : r ≫ coprod.map (𝟙 _) (phaseFold A k) = r')
  (block : c ≫ coprod.map (𝟙 _) (phaseFold A k) = phaseFold A k ≫ c')

include row block in
/-- Entered in `R`, the two loops agree. Entered in the block, the loop is
the fold followed by the folded loop. Together: uniformity along
`id_R + phaseFold`. -/
theorem partial_fold_feedback :
    (projection pe).map (sumInl R (phaseType A k) ≫ iterate (blockStep R (phaseType A k) r c)) =
        (projection pe).map (sumInl R A ≫ iterate (blockStep R A r' c')) ∧
    (projection pe).map (sumInr R (phaseType A k) ≫ iterate (blockStep R (phaseType A k) r c)) =
        (projection pe).map (phaseFold A k ≫ sumInr R A ≫ iterate (blockStep R A r' c')) ∧
    (projection pe).map (iterate (blockStep R (phaseType A k) r c)) =
        (projection pe).map (sumMap R (phaseFold A k) ≫ iterate (blockStep R A r' c')) :=
  Paper.Extension.Singleton.projection_right_block _ R (phaseFold A k) r c r' c' row
    (fold_uniform pe k c c' block)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity
