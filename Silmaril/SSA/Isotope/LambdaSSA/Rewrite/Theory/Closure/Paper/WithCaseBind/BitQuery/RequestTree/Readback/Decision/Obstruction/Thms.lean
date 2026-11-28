module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Readback.Decision.Obstruction.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryOperandSeparation

/-! # The constructor-known operand equation fails in default Paper -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree.Readback.Obstruction

open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

/-- The original closed packed arrows differ for either constructor and
either request label in unchanged Paper. -/
theorem packed_ne (label b : Bool) : sourcePacked label b ≠ targetPacked label b :=
  BitQueryOperandSeparation.packed_ne label b

/-- Adjoining just returned-call sequencing still leaves the constructor-known
term case distinct from the literal operand. -/
theorem packed_ne_with_call_sequencing (label b : Bool) :
    Paper.Extension.Singleton.ofRegion Paper.WithComputedCallReturns.Step (source_typed label b).packExits ≠
      Paper.Extension.Singleton.ofRegion Paper.WithComputedCallReturns.Step (target_typed label b).packExits :=
  BitQueryOperandSeparation.packed_ne_with_call_sequencing label b

theorem case_operand_beta_fails : ¬ CaseOperandBeta :=
  BitQueryOperandSeparation.case_operand_beta_fails

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree.Readback.Obstruction
