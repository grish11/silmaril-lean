module

import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.ConcreteExamples
import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.Renaming
import Lean

/-! Actual transitive axiom dependencies for the public typed/raw compiler
interfaces, unconditional corridors/theory comparisons and semantic controls.
Each selected declaration is bounded by exactly the standard foundational
ceiling propext, Classical.choice and Quot.sound. The printed actual sets are
not assumed to equal that ceiling; no unrelated-library audit is claimed. -/

#print axioms Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.compile_correct
#print axioms Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.rawAdequacy
#print axioms Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.characteristic_correct
#print axioms Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.typedCorridor
#print axioms Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.typed_modelExpansive
#print axioms Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.theory_sat_iff
#print axioms Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.theory_unsat_iff
#print axioms Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.theory_entails_iff
#print axioms Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.raw_characteristic_correct
#print axioms Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.rawCorridor
#print axioms Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.raw_modelExpansive
#print axioms Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.raw_theory_models_iff
#print axioms Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.raw_theory_sat_iff
#print axioms Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.raw_theory_unsat_iff
#print axioms Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.raw_entails_iff
#print axioms Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.rename_denote
#print axioms Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.renamed_compile_correct
#print axioms Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.Noncanonical.laws
#print axioms Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.Noncanonical.model
#print axioms Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.Examples.compiled_contradiction
#print axioms Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.Examples.repeated_variable_false
#print axioms Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.RawExamples.variable_contradiction
#print axioms Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.RawExamples.repeated_variable_false
#print axioms Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.RawExamples.lifted_variable_contradiction

#print axioms Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.ConcreteExamples.checked
#print axioms Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.ConcreteExamples.objects_legal
#print axioms Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.ConcreteExamples.actual_model_exists
#print axioms Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.ConcreteExamples.objects_have_distinct_members
#print axioms Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.ConcreteExamples.false_member
#print axioms Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.ConcreteExamples.lifted_false_member

run_elab do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for declaration in #[
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.compile_correct,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.rawAdequacy,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.characteristic_correct,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.typedCorridor,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.typed_modelExpansive,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.theory_sat_iff,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.theory_unsat_iff,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.theory_entails_iff,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.raw_characteristic_correct,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.rawCorridor,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.raw_modelExpansive,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.raw_theory_models_iff,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.raw_theory_sat_iff,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.raw_theory_unsat_iff,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.raw_entails_iff,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.rename_denote,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.renamed_compile_correct,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.Noncanonical.laws,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.Noncanonical.model,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.Examples.compiled_contradiction,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.Examples.repeated_variable_false,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.RawExamples.variable_contradiction,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.RawExamples.repeated_variable_false,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.RawExamples.lifted_variable_contradiction,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.ConcreteExamples.checked,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.ConcreteExamples.objects_legal,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.ConcreteExamples.actual_model_exists,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.ConcreteExamples.objects_have_distinct_members,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.ConcreteExamples.false_member,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.ConcreteExamples.lifted_false_member] do
    let _ ← Lean.getConstInfo declaration
    for ax in (← Lean.collectAxioms declaration) do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {declaration}: {ax}"
