module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Generation.Example.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedLetGenerationExample

/-! # Generation and visible behavior of a capturing return -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet.Generation.Example

open Paper.Extension.Singleton.Generation (Generated)
open Paper.WithComputedCallReturns.Example.ITree (PayloadValue)

/-- The same return induction generates the actual two-call capturing return. -/
theorem retained_generated : Generated Seed retainedArrow :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedLetGenerationExample.retained_generated

/-- The producer runs once and the consumer receives both its reply and
the caller's original input before the consumer's reply is returned. -/
theorem retained_visible (x : PayloadValue) :
    (interpretation.map retainedArrow).of x = expected x :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedLetGenerationExample.retained_visible x

end Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet.Generation.Example
