module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Square.Native.Retained.Example.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.RetainedNativeFrameIteration

/-! # Iteration of the written retained-bit switch -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.NativeFrame.Retained.Example

open Paper.TypeCategory (iterate)

/-- The exact one- and two-round steps from the retained-bit fixture
have equal native iterates. Each selected row retains its request. -/
theorem double_iterate : iterate g₂ = iterate g :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.RetainedNativeFrameIteration.double_iterate

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.NativeFrame.Retained.Example
