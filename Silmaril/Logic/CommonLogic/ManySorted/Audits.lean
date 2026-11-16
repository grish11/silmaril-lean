module

public import Silmaril.Logic.CommonLogic.ManySorted.Examples
import Lean

namespace Silmaril.Logic.CommonLogic.ManySorted

/- Source-only audit proposal. Print observed dependencies, then reject any axiom
outside the standard ceiling. No exact observed sets are assumed in advance. -/
#print axioms wellTyped_iff
#print axioms term_map
#print axioms formula_map
#print axioms term_eval
#print axioms formula_holds
#print axioms sentence_map
#print axioms sentence_holds
#print axioms models_natural
#print axioms signatures
#print axioms typedReduct
#print axioms decode
#print axioms decodeHom
#print axioms models
#print axioms decodedEmpty
#print axioms empty_sort_all
#print axioms empty_sort_not_exists
#print axioms unguarded_exists_junk
#print axioms typing_is_required
#print axioms constant_inhabited
#print axioms reduct_carrier_eq

run_elab do
  let allowed : List Lean.Name := [``propext, ``Classical.choice, ``Quot.sound]
  let checked : List Lean.Name := [
    ``wellTyped_iff,
    ``term_map,
    ``formula_map,
    ``term_eval,
    ``formula_holds,
    ``sentence_map,
    ``sentence_holds,
    ``models_natural,
    ``signatures,
    ``typedReduct,
    ``decode,
    ``decodeHom,
    ``models,
    ``decodedEmpty,
    ``empty_sort_all,
    ``empty_sort_not_exists,
    ``unguarded_exists_junk,
    ``typing_is_required,
    ``constant_inhabited,
    ``reduct_carrier_eq]
  for name in checked do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"

end Silmaril.Logic.CommonLogic.ManySorted
