module

public import Silmaril.Logic.Algebraic.Initial.Matching.FiniteSorted.Expansion.Thms
import Lean

/-! 21 selected transitive dependency ceilings. Build this module to print
dependencies and enforce the standard three-axiom ceiling. -/
#print axioms Silmaril.Logic.Institution.Structured.Constraints.freeAt_iso
#print axioms Silmaril.Logic.Institution.Structured.Constraints.sat_iso
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.expandModel
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.forgetRelations
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.decodeExpandIso
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.expandHom
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.equation_holds_iso
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.equationalRoom_isoInvariant
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.Sentence.satisfies_iso
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.sourceRoom_isoInvariant
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.expandModels
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.expansionDecodeIso
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.comparison_isoExpansive
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.comparison_elemExpansive
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.toMatching_elemExpansive
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.toMatching_faithful
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.expandModel_satisfaction
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.satisfiable_compile_iff
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.unsatisfiable_compile_iff
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.entails_compile_iff
#print axioms Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.entails_reflect

run_elab do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let checked : Array Lean.Name := #[
    ``Silmaril.Logic.Institution.Structured.Constraints.freeAt_iso,
    ``Silmaril.Logic.Institution.Structured.Constraints.sat_iso,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.expandModel,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.forgetRelations,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.decodeExpandIso,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.expandHom,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.equation_holds_iso,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.equationalRoom_isoInvariant,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.Sentence.satisfies_iso,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.sourceRoom_isoInvariant,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.expandModels,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.expansionDecodeIso,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.comparison_isoExpansive,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.comparison_elemExpansive,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.toMatching_elemExpansive,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.toMatching_faithful,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.expandModel_satisfaction,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.satisfiable_compile_iff,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.unsatisfiable_compile_iff,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.entails_compile_iff,
    ``Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.entails_reflect]
  for declaration in checked do
    for ax in (← Lean.collectAxioms declaration) do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {declaration}: {ax}"
  Lean.logInfo m!"finiteSortedExpansion: checked {checked.size} selected declarations against the standard three-axiom ceiling"
