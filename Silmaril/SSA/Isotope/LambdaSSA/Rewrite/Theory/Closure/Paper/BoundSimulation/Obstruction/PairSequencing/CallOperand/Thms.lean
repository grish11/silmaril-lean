module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.PairSequencing.CallOperand.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.CallOperand

/-! # Independence of computed-call sequencing in the constructor join -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction.PairSequencing.CallOperand

local notation "U" => (Ty.unit : Ty Empty)

/-- Even with constructor sequencing, the joined closure distinguishes
the computed call argument from running it once before the call. -/
theorem separation :
    ¬ Paper.WithConstructorSequencing.Joined.Eqv false [U] nestedReturn sequencedReturn [U] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.callOperand_fails

end Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction.PairSequencing.CallOperand
