module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Example.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.MixedBitTriplingExample

/-! # Tripling and absence of a single Unit recurrence factor -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ComponentTripling.Example

open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton (iterateChosen)
open Paper.Extension.Singleton.ThreeCycle (triple triple_step_bit)

/-- The unbatched and three-round boundary arrows have equal feedback. -/
theorem round_triples : iterateChosen Seed (triple round) = iterateChosen Seed round :=
  triple_step_bit Seed (fun h => h) round

/-- The mixed round cannot use one Unit repeat port followed by a common
restoring computation. The two recursive results can carry different tags. -/
theorem no_unit_factor (first : Obj Bit ⟶ Obj U ⨿ Obj U) (restore : Obj U ⟶ Obj Bit) :
    round ≠ first ≫ coprod.map (𝟙 (Obj U)) restore :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.MixedBitTriplingExample.no_unit_factor first restore

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ComponentTripling.Example
