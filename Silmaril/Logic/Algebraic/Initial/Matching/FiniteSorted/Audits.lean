module

public import Silmaril.Logic.Algebraic.Initial.Matching.FiniteSorted.Examples
import Lean

/-! Selected transitive ceilings: exactly 46 printed source declarations,
including private helpers through their dependencies. Elaboration prints their
actual axiom dependencies and rejects axioms outside the standard three.
This is a selected-declaration check, not a whole-library audit. -/

#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Profile
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Operation
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Profile.signature
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.operationsAt
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.recursionVariable
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.constructorPattern
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.body
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.system
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.generated
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.generationClause
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.compiled
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.embedFamily
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.extractFamily
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.operator_embed
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.raw_lfp_eq_generated
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.generated_denote
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.generationClause_satisfaction
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.compiled_satisfaction
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.compiled_initial_iff
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.compiled_actual_iff
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.left_operations
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.right_operations
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.collapse_not_injective
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.distinct_original_coordinates
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.collapsed_ground_range
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.original_equations_retained
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.unseeded_no_ground
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.unseeded_generated_empty
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.genuinely_empty_active
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.padding_inhabited
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.empty_active_generated
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.no_invented_coordinate
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.numericAmbient
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.numericNative
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.unary_symbols_identified
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.both_unary_are_successor
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.numeric_evaluate_parity
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.numeric_unpad_evaluate
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.numeric_evaluate_raw
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.zero_in_coordinate_zero
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.one_in_coordinate_one
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.two_in_coordinate_zero
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.three_in_coordinate_one
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.zero_not_in_coordinate_one
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.one_not_in_coordinate_zero
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.collapsed_compiled_denotations_distinct

run_elab do
  let allowed : List Lean.Name := [``propext, ``Classical.choice, ``Quot.sound]
  let checked : List Lean.Name := [
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Profile,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Operation,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Profile.signature,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.operationsAt,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.recursionVariable,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.constructorPattern,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.body,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.system,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.generated,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.generationClause,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.compiled,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.embedFamily,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.extractFamily,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.operator_embed,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.raw_lfp_eq_generated,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.generated_denote,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.generationClause_satisfaction,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.compiled_satisfaction,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.compiled_initial_iff,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.compiled_actual_iff,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.left_operations,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.right_operations,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.collapse_not_injective,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.distinct_original_coordinates,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.collapsed_ground_range,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.original_equations_retained,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.unseeded_no_ground,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.unseeded_generated_empty,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.genuinely_empty_active,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.padding_inhabited,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.empty_active_generated,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.no_invented_coordinate,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.numericAmbient,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.numericNative,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.unary_symbols_identified,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.both_unary_are_successor,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.numeric_evaluate_parity,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.numeric_unpad_evaluate,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.numeric_evaluate_raw,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.zero_in_coordinate_zero,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.one_in_coordinate_one,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.two_in_coordinate_zero,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.three_in_coordinate_one,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.zero_not_in_coordinate_one,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.one_not_in_coordinate_zero,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples.collapsed_compiled_denotations_distinct]
  for name in checked do
    for axiomName in (← Lean.collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  Lean.logInfo m!"finiteSorted: checked {checked.length} selected declarations against the standard three-axiom ceiling"
