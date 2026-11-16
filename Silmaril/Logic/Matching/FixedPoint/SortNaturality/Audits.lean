module

public import Silmaril.Logic.Matching.FixedPoint.SortNaturality.Examples
import Lean

/-! Selected transitive axiom ceilings for the exact renaming bridges and their
indexed controls. The scope is exactly the 23 printed names below.
Private proof helpers are included transitively. This is not a whole-library
or structural-assumption audit; substitution and compiler naturality are pending. -/

#print axioms Silmaril.Logic.Matching.FixedPoint.SortNaturality.mapRen
#print axioms Silmaril.Logic.Matching.FixedPoint.SortNaturality.mapRen_val
#print axioms Silmaril.Logic.Matching.FixedPoint.SortNaturality.pull_mapRen
#print axioms Silmaril.Logic.Matching.FixedPoint.SortNaturality.mapRen_shift
#print axioms Silmaril.Logic.Matching.FixedPoint.SortNaturality.mapRen_lift
#print axioms Silmaril.Logic.Matching.FixedPoint.SortNaturality.mapRen_liftHead
#print axioms Silmaril.Logic.Matching.FixedPoint.SortNaturality.fixedPattern_sort_cast
#print axioms Silmaril.Logic.Matching.FixedPoint.SortNaturality.fixedPattern_objects_cast
#print axioms Silmaril.Logic.Matching.FixedPoint.SortNaturality.fixedPattern_sets_cast
#print axioms Silmaril.Logic.Matching.FixedPoint.SortNaturality.renameSets_objects_cast
#print axioms Silmaril.Logic.Matching.FixedPoint.SortNaturality.renameObjects_sets_cast
#print axioms Silmaril.Logic.Matching.FixedPoint.SortNaturality.fixedPattern_renameSets
#print axioms Silmaril.Logic.Matching.FixedPoint.SortNaturality.pattern_renameFirstOrder
#print axioms Silmaril.Logic.Matching.FixedPoint.SortNaturality.fixedPattern_renameObjects
#print axioms Silmaril.Logic.Matching.FixedPoint.SortNaturality.Examples.collapse_not_injective
#print axioms Silmaril.Logic.Matching.FixedPoint.SortNaturality.Examples.collapsed_set_coordinates_distinct
#print axioms Silmaril.Logic.Matching.FixedPoint.SortNaturality.Examples.collapsed_object_coordinates_distinct
#print axioms Silmaril.Logic.Matching.FixedPoint.SortNaturality.Examples.same_sort_set_coordinates_distinct
#print axioms Silmaril.Logic.Matching.FixedPoint.SortNaturality.Examples.swap_moves_coordinate
#print axioms Silmaril.Logic.Matching.FixedPoint.SortNaturality.Examples.same_sort_swap_literal
#print axioms Silmaril.Logic.Matching.FixedPoint.SortNaturality.Examples.nested_set_shift_literal
#print axioms Silmaril.Logic.Matching.FixedPoint.SortNaturality.Examples.nested_object_shift_literal
#print axioms Silmaril.Logic.Matching.FixedPoint.SortNaturality.Examples.quantified_object_shift_literal

run_elab do
  let allowed : List Lean.Name := [``propext, ``Classical.choice, ``Quot.sound]
  let checked : List Lean.Name := [
    ``Silmaril.Logic.Matching.FixedPoint.SortNaturality.mapRen,
    ``Silmaril.Logic.Matching.FixedPoint.SortNaturality.mapRen_val,
    ``Silmaril.Logic.Matching.FixedPoint.SortNaturality.pull_mapRen,
    ``Silmaril.Logic.Matching.FixedPoint.SortNaturality.mapRen_shift,
    ``Silmaril.Logic.Matching.FixedPoint.SortNaturality.mapRen_lift,
    ``Silmaril.Logic.Matching.FixedPoint.SortNaturality.mapRen_liftHead,
    ``Silmaril.Logic.Matching.FixedPoint.SortNaturality.fixedPattern_sort_cast,
    ``Silmaril.Logic.Matching.FixedPoint.SortNaturality.fixedPattern_objects_cast,
    ``Silmaril.Logic.Matching.FixedPoint.SortNaturality.fixedPattern_sets_cast,
    ``Silmaril.Logic.Matching.FixedPoint.SortNaturality.renameSets_objects_cast,
    ``Silmaril.Logic.Matching.FixedPoint.SortNaturality.renameObjects_sets_cast,
    ``Silmaril.Logic.Matching.FixedPoint.SortNaturality.fixedPattern_renameSets,
    ``Silmaril.Logic.Matching.FixedPoint.SortNaturality.pattern_renameFirstOrder,
    ``Silmaril.Logic.Matching.FixedPoint.SortNaturality.fixedPattern_renameObjects,
    ``Silmaril.Logic.Matching.FixedPoint.SortNaturality.Examples.collapse_not_injective,
    ``Silmaril.Logic.Matching.FixedPoint.SortNaturality.Examples.collapsed_set_coordinates_distinct,
    ``Silmaril.Logic.Matching.FixedPoint.SortNaturality.Examples.collapsed_object_coordinates_distinct,
    ``Silmaril.Logic.Matching.FixedPoint.SortNaturality.Examples.same_sort_set_coordinates_distinct,
    ``Silmaril.Logic.Matching.FixedPoint.SortNaturality.Examples.swap_moves_coordinate,
    ``Silmaril.Logic.Matching.FixedPoint.SortNaturality.Examples.same_sort_swap_literal,
    ``Silmaril.Logic.Matching.FixedPoint.SortNaturality.Examples.nested_set_shift_literal,
    ``Silmaril.Logic.Matching.FixedPoint.SortNaturality.Examples.nested_object_shift_literal,
    ``Silmaril.Logic.Matching.FixedPoint.SortNaturality.Examples.quantified_object_shift_literal]
  for name in checked do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  Lean.logInfo m!"sortNaturality: checked {checked.length} selected declarations against the standard three-axiom ceiling"
