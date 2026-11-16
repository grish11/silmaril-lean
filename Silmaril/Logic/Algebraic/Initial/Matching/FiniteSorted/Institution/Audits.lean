module

public import Silmaril.Logic.Algebraic.Initial.Matching.FiniteSorted.Institution.Thms
import Lean

/-! Elaboration prints the selected institution dependencies and rejects
any axiom outside the standard three. -/
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.Sentence.actual_map
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.Sentence.satisfaction
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.decodeModels_full
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.decodeModels_faithful
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.decodeModels_map_lift
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.decode_reduct_square
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.theoryCorridor_id
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.theoryCorridor_comp
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.Sentence.compile_map
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.Sentence.compile_satisfaction
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.translation
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.toMatching
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.entails_map

run_elab do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for declaration in #[
      ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.Sentence.actual_map,
      ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.Sentence.satisfaction,
      ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.decodeModels_full,
      ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.decodeModels_faithful,
      ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.decodeModels_map_lift,
      ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.decode_reduct_square,
      ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.theoryCorridor_id,
      ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.theoryCorridor_comp,
      ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.Sentence.compile_map,
      ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.Sentence.compile_satisfaction,
      ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.translation,
      ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.toMatching,
      ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.entails_map] do
    for ax in (← Lean.collectAxioms declaration) do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {declaration}: {ax}"
