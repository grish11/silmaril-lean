module

public import Silmaril.Logic.Algebraic.OrderSorted.Representation.Examples
import Lean

open Silmaril.Logic.Algebraic.OrderSorted.Representation
#print axioms locallyFiltered_iff_componentFiltered
#print axioms embed_injective
#print axioms embed_coerce
#print axioms representationIso
#print axioms eval_represent
#print axioms satisfies_represent_iff
#print axioms representationEquivalence
#print axioms theory_satisfiable_iff
#print axioms theory_entails_iff

run_elab do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for declaration in #[``locallyFiltered_iff_componentFiltered, ``embed_injective,
      ``embed_coerce, ``representationIso, ``eval_represent, ``satisfies_represent_iff,
      ``representationEquivalence, ``theory_satisfiable_iff, ``theory_entails_iff,
      ``Examples.Relocation.coherence, ``Examples.Relocation.relocation,
      ``Examples.empty_not_global, ``Examples.empty_carrier] do
    for ax in (← Lean.collectAxioms declaration) do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {declaration}: {ax}"
