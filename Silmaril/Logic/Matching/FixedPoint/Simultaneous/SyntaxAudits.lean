module

public import Silmaril.Logic.Matching.FixedPoint.Simultaneous.SyntaxExamples
import Lean

/-! Selected transitive axiom ceilings for literal substitution and compiler
naturality. Exactly 14 printed declarations are guarded, including their
private helper dependencies. This is not a whole-library or structural audit. -/

#print axioms Silmaril.Logic.Matching.FixedPoint.SortNaturality.fixedPattern_objectShift
#print axioms Silmaril.Logic.Matching.FixedPoint.SortNaturality.fixedPattern_setShift
#print axioms Silmaril.Logic.Matching.FixedPoint.SortNaturality.fixedPattern_substituteSets
#print axioms Silmaril.Logic.Matching.FixedPoint.Simultaneous.map_append
#print axioms Silmaril.Logic.Matching.FixedPoint.Simultaneous.mapRen_tailRen
#print axioms Silmaril.Logic.Matching.FixedPoint.Simultaneous.System.tail_map_heq
#print axioms Silmaril.Logic.Matching.FixedPoint.Simultaneous.headSub_map_heq
#print axioms Silmaril.Logic.Matching.FixedPoint.Simultaneous.System.compile_map
#print axioms Silmaril.Logic.Matching.FixedPoint.Simultaneous.SyntaxExamples.collapse_not_injective
#print axioms Silmaril.Logic.Matching.FixedPoint.Simultaneous.SyntaxExamples.mutual_compile_literal
#print axioms Silmaril.Logic.Matching.FixedPoint.Simultaneous.SyntaxExamples.unseeded_compile_literal
#print axioms Silmaril.Logic.Matching.FixedPoint.Simultaneous.SyntaxExamples.same_sort_compile_literal
#print axioms Silmaril.Logic.Matching.FixedPoint.Simultaneous.SyntaxExamples.same_sort_source_indices_distinct
#print axioms Silmaril.Logic.Matching.FixedPoint.Simultaneous.SyntaxExamples.empty_compile_literal

run_elab do
  let allowed : List Lean.Name := [``propext, ``Classical.choice, ``Quot.sound]
  let checked : List Lean.Name := [
    ``Silmaril.Logic.Matching.FixedPoint.SortNaturality.fixedPattern_objectShift,
    ``Silmaril.Logic.Matching.FixedPoint.SortNaturality.fixedPattern_setShift,
    ``Silmaril.Logic.Matching.FixedPoint.SortNaturality.fixedPattern_substituteSets,
    ``Silmaril.Logic.Matching.FixedPoint.Simultaneous.map_append,
    ``Silmaril.Logic.Matching.FixedPoint.Simultaneous.mapRen_tailRen,
    ``Silmaril.Logic.Matching.FixedPoint.Simultaneous.System.tail_map_heq,
    ``Silmaril.Logic.Matching.FixedPoint.Simultaneous.headSub_map_heq,
    ``Silmaril.Logic.Matching.FixedPoint.Simultaneous.System.compile_map,
    ``Silmaril.Logic.Matching.FixedPoint.Simultaneous.SyntaxExamples.collapse_not_injective,
    ``Silmaril.Logic.Matching.FixedPoint.Simultaneous.SyntaxExamples.mutual_compile_literal,
    ``Silmaril.Logic.Matching.FixedPoint.Simultaneous.SyntaxExamples.unseeded_compile_literal,
    ``Silmaril.Logic.Matching.FixedPoint.Simultaneous.SyntaxExamples.same_sort_compile_literal,
    ``Silmaril.Logic.Matching.FixedPoint.Simultaneous.SyntaxExamples.same_sort_source_indices_distinct,
    ``Silmaril.Logic.Matching.FixedPoint.Simultaneous.SyntaxExamples.empty_compile_literal]
  for name in checked do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  Lean.logInfo m!"simultaneousSyntax: checked {checked.length} selected declarations against the standard three-axiom ceiling"
