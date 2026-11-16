module

public import Silmaril.Logic.Algebraic.Lambda.Varying.Examples
import Lean

/-! Reject nonstandard axioms in the institution laws, actual model square,
full EQ comparison, borrowing theorems and concrete controls. -/
open Silmaril.Logic.Algebraic.Lambda.Varying

run_elab do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for declaration in #[``Silmaril.Logic.STLCEquations.inst,
      ``Silmaril.Logic.STLCEquations.eval_map, ``Silmaril.Logic.STLCEquations.satisfaction,
      ``Silmaril.Logic.STLCEquations.mapTerm_identity, ``Silmaril.Logic.STLCEquations.mapTerm_comp,
      ``Silmaril.Logic.STLCEquations.reduct_identity, ``Silmaril.Logic.STLCEquations.reduct_comp,
      ``Silmaril.Logic.STLCEquations.reductFunctor_identity,
      ``Silmaril.Logic.STLCEquations.reductFunctor_comp,
      ``toLambda, ``term_naturality, ``compile_naturality, ``reduct_naturality,
      ``modelReduct_naturality, ``toSTLC, ``toSTLC_modelExpansive,
      ``entails_iff, ``sat_iff, ``unsat_iff,
      ``Examples.collapse_not_injective, ``Examples.swap_twice,
      ``Examples.collapsed_equation_false, ``Examples.compiled_collapsed_equation_false,
      ``Examples.compiled_reflexive_true, ``Examples.pure_theory_sat, ``Examples.unused_sort_empty,
      ``Examples.used_sort_retained, ``Examples.nullary_evaluates,
      ``Examples.source_inference_fails, ``Examples.collapsed_inference_succeeds] do
    for ax in (← Lean.collectAxioms declaration) do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {declaration}: {ax}"
