module

public import Silmaril.Logic.Algebraic.OrderSorted.Representation.Institution.Examples
import Lean

open Silmaril.Logic.Algebraic.OrderSorted.Representation
#print axioms literalReductFunctor_id
#print axioms literalReductFunctor_comp
#print axioms literal_satisfaction
#print axioms compile_reductFunctor
#print axioms toLiteral
#print axioms literal_theory_satisfiable_iff
#print axioms literal_theory_entails_iff
#print axioms toLiteral_isoExpansive
#print axioms toLiteral_elemExpansive
#print axioms toLiteral_faithful
#print axioms toLiteral_room_entails_iff

run_elab do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for declaration in #[``literalReductFunctor_id, ``literalReductFunctor_comp,
      ``literalAlgebra_reduct, ``literal_satisfaction, ``literalInstitution,
      ``compile_reductFunctor, ``toLiteralNat, ``toLiteral,
      ``literal_theory_satisfiable_iff, ``literal_theory_entails_iff,
      ``toLiteral_isoExpansive, ``toLiteral_elemExpansive, ``toLiteral_faithful,
      ``toLiteral_room_entails_iff,
      ``InstitutionExamples.constantsEqual_reduct, ``InstitutionExamples.compiled_reduct] do
    for ax in (← Lean.collectAxioms declaration) do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {declaration}: {ax}"
