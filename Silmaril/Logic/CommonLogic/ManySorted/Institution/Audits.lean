module

public import Silmaril.Logic.CommonLogic.ManySorted.Institution.Examples
import Lean

/-! Named-declaration axiom ceiling for institution.
Checks every user-authored public top-level definition/type/theorem in this slice
and its examples, including public implementation bridge theorems where present.
Private helpers are checked transitively through these declarations.
The scope is exactly the 29 names printed and listed below; this is not a
whole-library or structural-assumption audit. No exact observed axiom sets are presumed. -/

#print axioms Silmaril.Logic.CommonLogic.ManySorted.Institution.room
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Institution.corridor
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Institution.reduct_id
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Institution.reduct_comp
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Institution.corridor_id
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Institution.corridor_comp
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Institution.institution
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Institution.inst
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Institution.comorphism
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Institution.isoExpansive
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Institution.elemExpansive
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Institution.faithful
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Institution.entails_iff
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Institution.satisfiable_iff
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Institution.unsatisfiable_iff
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Institution.forgetComparison
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Institution.typedForget
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Institution.Examples.twoSorted
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Institution.Examples.oneSorted
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Institution.Examples.collapse
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Institution.Examples.collapse_not_injective
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Institution.Examples.numeric
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Institution.Examples.target
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Institution.Examples.pulledBack
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Institution.Examples.pulledBack_carriers
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Institution.Examples.pulledBack_inhabited
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Institution.Examples.collapse_decode
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Institution.Examples.collapse_comparison
#print axioms Silmaril.Logic.CommonLogic.ManySorted.Institution.Examples.collapse_satisfaction

run_elab do
  let allowed : List Lean.Name := [``propext, ``Classical.choice, ``Quot.sound]
  let checked : List Lean.Name := [
    ``Silmaril.Logic.CommonLogic.ManySorted.Institution.room,
    ``Silmaril.Logic.CommonLogic.ManySorted.Institution.corridor,
    ``Silmaril.Logic.CommonLogic.ManySorted.Institution.reduct_id,
    ``Silmaril.Logic.CommonLogic.ManySorted.Institution.reduct_comp,
    ``Silmaril.Logic.CommonLogic.ManySorted.Institution.corridor_id,
    ``Silmaril.Logic.CommonLogic.ManySorted.Institution.corridor_comp,
    ``Silmaril.Logic.CommonLogic.ManySorted.Institution.institution,
    ``Silmaril.Logic.CommonLogic.ManySorted.Institution.inst,
    ``Silmaril.Logic.CommonLogic.ManySorted.Institution.comorphism,
    ``Silmaril.Logic.CommonLogic.ManySorted.Institution.isoExpansive,
    ``Silmaril.Logic.CommonLogic.ManySorted.Institution.elemExpansive,
    ``Silmaril.Logic.CommonLogic.ManySorted.Institution.faithful,
    ``Silmaril.Logic.CommonLogic.ManySorted.Institution.entails_iff,
    ``Silmaril.Logic.CommonLogic.ManySorted.Institution.satisfiable_iff,
    ``Silmaril.Logic.CommonLogic.ManySorted.Institution.unsatisfiable_iff,
    ``Silmaril.Logic.CommonLogic.ManySorted.Institution.forgetComparison,
    ``Silmaril.Logic.CommonLogic.ManySorted.Institution.typedForget,
    ``Silmaril.Logic.CommonLogic.ManySorted.Institution.Examples.twoSorted,
    ``Silmaril.Logic.CommonLogic.ManySorted.Institution.Examples.oneSorted,
    ``Silmaril.Logic.CommonLogic.ManySorted.Institution.Examples.collapse,
    ``Silmaril.Logic.CommonLogic.ManySorted.Institution.Examples.collapse_not_injective,
    ``Silmaril.Logic.CommonLogic.ManySorted.Institution.Examples.numeric,
    ``Silmaril.Logic.CommonLogic.ManySorted.Institution.Examples.target,
    ``Silmaril.Logic.CommonLogic.ManySorted.Institution.Examples.pulledBack,
    ``Silmaril.Logic.CommonLogic.ManySorted.Institution.Examples.pulledBack_carriers,
    ``Silmaril.Logic.CommonLogic.ManySorted.Institution.Examples.pulledBack_inhabited,
    ``Silmaril.Logic.CommonLogic.ManySorted.Institution.Examples.collapse_decode,
    ``Silmaril.Logic.CommonLogic.ManySorted.Institution.Examples.collapse_comparison,
    ``Silmaril.Logic.CommonLogic.ManySorted.Institution.Examples.collapse_satisfaction]
  for name in checked do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  Lean.logInfo m!"institution: checked {checked.length} named declarations against the standard three-axiom ceiling"
