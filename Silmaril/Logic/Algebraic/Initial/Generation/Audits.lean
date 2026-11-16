module

public import Silmaril.Logic.Algebraic.Initial.Generation.Examples
import Lean

/-! Actual transitive dependencies for selected generic theorems and controls,
with the standard-three ceiling. No exact dependency set or whole-library
audit is claimed. -/

#print axioms Silmaril.Logic.Algebraic.Initial.Generation.groundStep_evaluationRange_le
#print axioms Silmaril.Logic.Algebraic.Initial.Generation.evaluate_mem_generated
#print axioms Silmaril.Logic.Algebraic.Initial.Generation.groundStep_lfp_eq_range
#print axioms Silmaril.Logic.Algebraic.Initial.Generation.generated_iff_eq_top
#print axioms Silmaril.Logic.Algebraic.Initial.Generation.Examples.InfiniteChain.generated_singleton
#print axioms Silmaril.Logic.Algebraic.Initial.Generation.Examples.Mutual.extra_right_not_generated
#print axioms Silmaril.Logic.Algebraic.Initial.Generation.Examples.Unseeded.generated_bot
#print axioms Silmaril.Logic.Algebraic.Initial.Generation.Examples.ZeroSorts.generated_top

run_elab do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations : Array Lean.Name := #[
    ``Silmaril.Logic.Algebraic.Initial.Generation.groundStep_evaluationRange_le,
    ``Silmaril.Logic.Algebraic.Initial.Generation.evaluate_mem_generated,
    ``Silmaril.Logic.Algebraic.Initial.Generation.groundStep_lfp_eq_range,
    ``Silmaril.Logic.Algebraic.Initial.Generation.generated_iff_eq_top,
    ``Silmaril.Logic.Algebraic.Initial.Generation.Examples.InfiniteChain.generated_singleton,
    ``Silmaril.Logic.Algebraic.Initial.Generation.Examples.Mutual.extra_right_not_generated,
    ``Silmaril.Logic.Algebraic.Initial.Generation.Examples.Unseeded.generated_bot,
    ``Silmaril.Logic.Algebraic.Initial.Generation.Examples.ZeroSorts.generated_top]
  for declaration in declarations do
    for ax in (← Lean.collectAxioms declaration) do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {declaration}: {ax}"
