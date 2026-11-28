module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Sums.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonOutline

/-! # Outlining: a row run in place of a jump is a jump to a new state

An equation of default Paper. It follows from rolling, the fixpoint law
and the codiagonal law.
-/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Let `c` be the step of the old states `P`, which may also jump to a
new state `R`, and let `r₀` be the row of `R`, which returns or jumps
to an old state. Running `r₀` in place of each jump to `R` gives the
loop of the table with the new state, entered at an old state. -/
theorem iterate_outline {R P Y : τ} (r₀ : ofType (Φ := Φ) R ⟶ ofType Y ⨿ ofType P)
    (c : ofType (Φ := Φ) P ⟶ ofType Y ⨿ ofType (Silmaril.coprod R P)) :
    iterate (c ≫ coprod.desc coprod.inl (sumDesc r₀ coprod.inr)) =
      sumInr R P ≫ iterate (sumDesc (r₀ ≫ coprod.map (𝟙 _) (sumInr R P)) c) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonOutline.outline r₀ c

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
