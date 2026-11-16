module

public import Silmaril.Logic.Algebraic.Initial.Matching.FiniteSorted.Naturality.Thms
import Lean

/-! Elaboration prints the selected naturality dependencies and rejects
axioms outside the standard three. -/
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.coordinate_map
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.emptyContext_map
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.bodyContext_map
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.recursionVariable_map
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.constructorPattern_map
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.bottom_map
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.disjunction_map
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.body_map
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.system_map
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.generated_map
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.generationClause_map
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.encoded_spectrum_map
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.compiled_map

run_elab do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for declaration in #[
      ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.coordinate_map,
      ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.emptyContext_map,
      ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.bodyContext_map,
      ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.recursionVariable_map,
      ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.constructorPattern_map,
      ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.bottom_map,
      ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.disjunction_map,
      ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.body_map,
      ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.system_map,
      ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.generated_map,
      ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.generationClause_map,
      ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.encoded_spectrum_map,
      ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.compiled_map] do
    for ax in (← Lean.collectAxioms declaration) do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {declaration}: {ax}"
