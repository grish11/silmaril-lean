module

public import Silmaril.Logic.Algebraic.Initial.Quotient.Characterization.Examples
import Lean.Util.CollectAxioms

/-! Exact declaration identities and a standard-axiom ceiling for Packet 1.
The print commands report actual transitive dependencies when this module is
compiled; no measured axiom set or successful audit is asserted by this source.
The guard rejects every axiom outside the explicit policy below, including
sorryAx. Exact measured #guard_msgs receipts can be added only after observation.
-/

#print axioms Silmaril.Logic.Algebraic.Initial.Presented.Characterization.models_of_generated_kernel
#print axioms Silmaril.Logic.Algebraic.Initial.Presented.Characterization.fold_bijective
#print axioms Silmaril.Logic.Algebraic.Initial.Presented.Characterization.foldIso
#print axioms Silmaril.Logic.Algebraic.Initial.Presented.Characterization.iso_map_bijective
#print axioms Silmaril.Logic.Algebraic.Initial.Presented.Characterization.generated_kernel_of_initial
#print axioms Silmaril.Logic.Algebraic.Initial.Presented.Characterization.initial_iff_generated_kernel
#print axioms Silmaril.Logic.Algebraic.Initial.Presented.Characterization.modelhood_initial_iff
#print axioms Silmaril.Logic.Algebraic.Initial.Presented.Characterization.Examples.generated_model_not_initial
#print axioms Silmaril.Logic.Algebraic.Initial.Presented.Characterization.Examples.identified_initial_properties
#print axioms Silmaril.Logic.Algebraic.Initial.Presented.Characterization.Examples.identified_constants_equal
#print axioms Silmaril.Logic.Algebraic.Initial.Presented.Characterization.Examples.EmptySort.quotient_properties
#print axioms Silmaril.Logic.Algebraic.Initial.Presented.Characterization.Examples.EmptySort.singleton_not_generated
#print axioms Silmaril.Logic.Algebraic.Initial.Presented.Characterization.Examples.EmptySort.singleton_not_initial

run_cmd do
  let allowed : List Lean.Name := [``propext, ``Classical.choice, ``Quot.sound]
  let declarations : List Lean.Name := [
    ``Silmaril.Logic.Algebraic.Initial.Presented.Characterization.models_of_generated_kernel,
    ``Silmaril.Logic.Algebraic.Initial.Presented.Characterization.fold_bijective,
    ``Silmaril.Logic.Algebraic.Initial.Presented.Characterization.foldIso,
    ``Silmaril.Logic.Algebraic.Initial.Presented.Characterization.iso_map_bijective,
    ``Silmaril.Logic.Algebraic.Initial.Presented.Characterization.generated_kernel_of_initial,
    ``Silmaril.Logic.Algebraic.Initial.Presented.Characterization.initial_iff_generated_kernel,
    ``Silmaril.Logic.Algebraic.Initial.Presented.Characterization.modelhood_initial_iff,
    ``Silmaril.Logic.Algebraic.Initial.Presented.Characterization.Examples.generated_model_not_initial,
    ``Silmaril.Logic.Algebraic.Initial.Presented.Characterization.Examples.identified_initial_properties,
    ``Silmaril.Logic.Algebraic.Initial.Presented.Characterization.Examples.identified_constants_equal,
    ``Silmaril.Logic.Algebraic.Initial.Presented.Characterization.Examples.EmptySort.quotient_properties,
    ``Silmaril.Logic.Algebraic.Initial.Presented.Characterization.Examples.EmptySort.singleton_not_generated,
    ``Silmaril.Logic.Algebraic.Initial.Presented.Characterization.Examples.EmptySort.singleton_not_initial]
  for declaration in declarations do
    unless (← Lean.getEnv).contains declaration do
      throwError "missing audited declaration: {declaration}"
    let actual ← Lean.collectAxioms declaration
    for dependency in actual do
      unless allowed.contains dependency do
        throwError "unexpected axiom {dependency} in {declaration}"
