module

public import Silmaril.Logic.Algebraic.Initial.Matching.FinitePresented.Examples
import Lean

/-! Named-declaration axiom ceiling for finitePresented.
Checks every user-authored public top-level definition/type/theorem in this slice
and its examples, including public implementation bridge theorems where present.
Private helpers are checked transitively through these declarations.
The scope is exactly the 63 names printed and listed below; this is not a
whole-library or structural-assumption audit. No exact observed axiom sets are presumed. -/

#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Profile
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Profile.signature
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Profile.ofConstructors
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Profile.ofConstructors_signature
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Tree
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.fold
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.treeAlgebra
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Equations
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.theory
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.targetSort
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Pat
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.bottom
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.disjunction
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.generatedBody
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.generated
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.generationClause
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.compiled
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.actual
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Satisfies
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.reduct
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.constants
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.left
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.right
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.equation
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.equations
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.separating
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.syntax_distinct
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.related
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.compiled_quotient
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.positive_present
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.collapse
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.empty_unrelated
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.collision_rejected
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.emptyAlgebra
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.ground_empty
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.emptyNative
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.empty_active
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.raw_nonempty
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.empty_compiled
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.zeroOperations
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.zero_positive
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.zero_operations_compiled
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.unaryOnly
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.unary_positive
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.unaryEquation
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.unaryEquations
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.unary_no_complete_ground_instance
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.unary_equation_compiled
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.unary_active_empty
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.foldHom
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.ground
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.ground_evaluate
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.generated_iff_fold_surjective
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.bottom_denote
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.disjunction_mem
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.generatedBody_mem
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.generated_denote
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.active_denote
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.generationClause_satisfaction
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.compiled_satisfaction
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.compiled_initial_iff
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.compiled_actual_iff
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.quotient_expansion_satisfies

run_elab do
  let allowed : List Lean.Name := [``propext, ``Classical.choice, ``Quot.sound]
  let checked : List Lean.Name := [
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Profile,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Profile.signature,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Profile.ofConstructors,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Profile.ofConstructors_signature,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Tree,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.fold,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.treeAlgebra,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Equations,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.theory,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.targetSort,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Pat,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.bottom,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.disjunction,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.generatedBody,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.generated,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.generationClause,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.compiled,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.actual,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Satisfies,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.reduct,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.constants,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.left,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.right,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.equation,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.equations,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.separating,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.syntax_distinct,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.related,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.compiled_quotient,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.positive_present,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.collapse,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.empty_unrelated,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.collision_rejected,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.emptyAlgebra,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.ground_empty,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.emptyNative,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.empty_active,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.raw_nonempty,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.empty_compiled,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.zeroOperations,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.zero_positive,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.zero_operations_compiled,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.unaryOnly,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.unary_positive,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.unaryEquation,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.unaryEquations,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.unary_no_complete_ground_instance,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.unary_equation_compiled,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples.unary_active_empty,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.foldHom,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.ground,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.ground_evaluate,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.generated_iff_fold_surjective,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.bottom_denote,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.disjunction_mem,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.generatedBody_mem,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.generated_denote,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.active_denote,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.generationClause_satisfaction,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.compiled_satisfaction,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.compiled_initial_iff,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.compiled_actual_iff,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.quotient_expansion_satisfies]
  for name in checked do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  Lean.logInfo m!"finitePresented: checked {checked.length} named declarations against the standard three-axiom ceiling"
