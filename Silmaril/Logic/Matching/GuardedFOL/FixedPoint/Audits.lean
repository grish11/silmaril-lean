module

public import Silmaril.Logic.Matching.GuardedFOL.FixedPoint.Thms
import Lean

/-! Print observed dependencies and enforce a foundational ceiling. This source
contains no assertion that the observations have already been executed. -/
#print axioms Silmaril.Logic.Matching.SortMaps.Hom.encodeFirstOrder_map
#print axioms Silmaril.Logic.Matching.GuardedFOL.firstOrderToFixedPoint_modelExpansive
#print axioms Silmaril.Logic.Matching.GuardedFOL.firstOrder_fixed_sat_iff
#print axioms Silmaril.Logic.Matching.GuardedFOL.firstOrder_fixed_unsat_iff
#print axioms Silmaril.Logic.Matching.GuardedFOL.firstOrder_fixed_entails_iff
#print axioms Silmaril.Logic.Matching.GuardedFOL.folFixedSentence_map
#print axioms Silmaril.Logic.Matching.GuardedFOL.folFixed_satisfaction
#print axioms Silmaril.Logic.Matching.GuardedFOL.fixedInstitution
#print axioms Silmaril.Logic.Matching.GuardedFOL.firstOrderToFixedPoint
#print axioms Silmaril.Logic.Matching.GuardedFOL.folToGuardedFixedPoint

run_elab do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for declaration in #[
      ``Silmaril.Logic.Matching.SortMaps.Hom.encodeFirstOrder_map,
      ``Silmaril.Logic.Matching.GuardedFOL.firstOrderToFixedPoint_modelExpansive,
      ``Silmaril.Logic.Matching.GuardedFOL.firstOrder_fixed_sat_iff,
      ``Silmaril.Logic.Matching.GuardedFOL.firstOrder_fixed_unsat_iff,
      ``Silmaril.Logic.Matching.GuardedFOL.firstOrder_fixed_entails_iff,
      ``Silmaril.Logic.Matching.GuardedFOL.folFixedSentence_map,
      ``Silmaril.Logic.Matching.GuardedFOL.folFixed_satisfaction,
      ``Silmaril.Logic.Matching.GuardedFOL.fixedInstitution,
      ``Silmaril.Logic.Matching.GuardedFOL.firstOrderToFixedPoint,
      ``Silmaril.Logic.Matching.GuardedFOL.folToGuardedFixedPoint] do
    for ax in (← Lean.collectAxioms declaration) do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {declaration}: {ax}"
