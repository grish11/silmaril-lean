module

public import Silmaril.Logic.Algebraic.ManySorted.Varying.Examples
import Lean

/-! Strict standard-axiom ceilings; these reject any additional dependency. -/
open Silmaril.Logic.Algebraic.ManySorted.Varying

run_elab do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for declaration in #[``mapTerm_comp, ``eval_map, ``satisfaction,
      ``reductFunctor_comp, ``fiber_institution,
      ``privateSignatures_roundtrip, ``publicSignatures_roundtrip,
      ``toEquation_map, ``fromEquation_map, ``fromModels_reduct, ``toModels_reduct,
      ``toPublicEQ, ``toManySorted, ``toPublicEQ_modelExpansive,
      ``toManySorted_modelExpansive, ``entails_iff, ``sat_iff, ``unsat_iff,
      ``privateRoom_roundtrip, ``publicRoom_roundtrip,
      ``public_entails_iff, ``public_sat_iff, ``public_unsat_iff,
      ``Examples.collision_false, ``Examples.empty_context_vacuous,
      ``Examples.collapse_not_model_expansive, ``Examples.actual_public_collision] do
    for ax in (← Lean.collectAxioms declaration) do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {declaration}: {ax}"
