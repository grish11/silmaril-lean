module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Constructor.Boundary.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Boundary.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Native.Replay.ConstructorBoundary

/-! # Repaired returns and the remaining computed-operand obstruction -/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native

open Region.Paper
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural Native.Boundary

/-- The exact pair counterexample from the previous joined quotient is
derivable after adjoining constructor sequencing. -/
theorem pair_repaired : Boundary.paired.ConstructorEqv Boundary.sequenced :=
  pair_repaired_proof

/-- The original unit η counterexample remains repaired. -/
theorem unit_repaired : Boundary.unitReturn.ConstructorEqv Boundary.unitForward :=
  unit_repaired_proof

namespace CallBoundary

open Region.Paper.BoundSimulation.Obstruction.PairSequencing
open scoped Native.CallBoundary

/-- Both original typed arrows agree in the common categorical class, but
the combined native relation cannot sequence this computed call operand. -/
theorem separation : nestedEndpoint.Valid sequencedEndpoint ∧
    ¬ nestedEndpoint.ConstructorEqv sequencedEndpoint :=
  ⟨valid_proof, separate_proof⟩

/-- The exact LetCase equation used by normalization. -/
theorem bindOp :
    LetCase.LocallyNameless.Equiv false LetCase.Structural.Reply.Γ₀ input nested.1 sequenced.1 U :=
  bindOp_proof

/-- The two exact operand round trips transport the obstruction to the
actual guarded reifier. -/
theorem reification_fails : ¬ ConstructorReplay nested sequenced :=
  reification_fails_proof

/-- The repository already supplies this missing root rule separately, on
the canonical return-region presentation. -/
theorem computedCall_step :
    WithComputedCallReturns.Step [U]
      (Region.CfgEta.TypeCategory.returnRegion CallOperand.nested)
      (Region.CfgEta.TypeCategory.returnRegion CallOperand.sequenced) [U] :=
  computedCall_proof

end CallBoundary
end Silmaril.Isotope.LambdaSSA.Acyclic.Native
