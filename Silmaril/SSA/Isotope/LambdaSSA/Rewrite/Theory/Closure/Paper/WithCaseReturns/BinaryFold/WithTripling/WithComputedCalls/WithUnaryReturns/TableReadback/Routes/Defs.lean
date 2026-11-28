module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Defs

/-! # Routing the ordered exits of a captured CFG -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback

universe v

variable {Φ : Type v}

/-- Exit D directly. For a local transfer retain the original capture and
inject the update at its original label index. -/
def carryExit (capture locals i : Nat) : Region Φ :=
  if i < locals then .br 0 (.inr (.pair (.var (capture + 1)) (packedExitArg i (.var 0))))
  else .br 0 (.inl (.var 0))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
