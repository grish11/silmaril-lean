module

public import Silmaril.Wasm.Logic.Algebraic.Initial.Wasm

@[expose] public section
namespace Silmaril.Logic.Algebraic.Initial.Examples
open CategoryTheory CategoryTheory.Limits Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Institution.Structured

/-- Constant interpretations can collapse every constructor to a single point. -/
abbrev collapsed : EQ.Algebra Wasm.signature := ⟨fun _ => PUnit, fun _ _ => PUnit.unit⟩

theorem no_collapsed_hom (f : collapsed ⟶ Wasm.arithmetic) : False := by
  have h0 := f.map_op (.literal (0#32)) (fun i => i.elim0)
  have h1 := f.map_op (.literal (1#32)) (fun i => i.elim0)
  have bad : (0#32) = (1#32) := h0.symm.trans h1
  exact (by decide : (0#32) ≠ (1#32)) bad

theorem collapsed_not_initial : ¬ Nonempty (IsInitial collapsed) := by
  rintro ⟨h⟩
  exact no_collapsed_hom (h.to Wasm.arithmetic)

abbrev collapsedModel : Models (emptyPresentation Wasm.signature) :=
  SemanticModels.emptyModel equational Wasm.signature collapsed

theorem collapsed_rejects_constraint :
    ¬ Constraints.Sat equational collapsed (initialConstraint (emptyPresentation Wasm.signature)) := by
  intro h
  obtain ⟨hi⟩ := (initialConstraint_sat_iff _ collapsedModel).1 h
  exact no_collapsed_hom (hi.to
    (SemanticModels.emptyModel equational Wasm.signature Wasm.arithmetic)).hom

/-- The initial constructor algebra is populated and satisfies the actual constraint. -/
theorem satisfiable : ∃ M : EQ.Algebra Wasm.signature,
    Nonempty (M.carrier ()) ∧
      Constraints.Sat equational M (initialConstraint (emptyPresentation Wasm.signature)) :=
  ⟨closedAlgebra Wasm.signature, ⟨Wasm.lit (0#32)⟩, closedModel_satisfies Wasm.signature⟩

abbrev noOperations : EQ.Signature := ⟨Bool, fun _ _ _ => PEmpty⟩

/-- No terms are manufactured in sorts without generators or constructors. -/
theorem no_closed_terms (s : Bool) : IsEmpty ((closedAlgebra noOperations).carrier s) := by
  exact ⟨fun t => EQ.Term.rec (Sg := noOperations) (motive := fun _ _ => False)
    (fun i => i.elim0) (fun o _ _ => o.elim) t⟩

theorem empty_initial_exists : Nonempty (IsInitial (closedAlgebra noOperations)) :=
  ⟨closed_isInitial noOperations⟩

/-- Free variables supply generators even when the signature has no operations. -/
theorem variable_is_generator :
    Nonempty ((termAlgebra noOperations (fun _ : Fin 1 => true)).carrier true) :=
  ⟨.var 0⟩

/-- Equations alone do not impose the no-confusion property of constructor syntax. -/
abbrev distinctLiterals : EQ.Equation Wasm.signature :=
  ⟨0, closedContext Wasm.signature, (), Wasm.lit (0#32), Wasm.lit (1#32)⟩

theorem collapsed_satisfies_false_constructor_equation : distinctLiterals.Holds collapsed :=
  fun _ => rfl

theorem arithmetic_refutes_constructor_equation : ¬ distinctLiterals.Holds Wasm.arithmetic := by
  intro h
  exact (by decide : (0#32) ≠ (1#32)) (h (fun i => i.elim0))

/-- info: 'Silmaril.Logic.Algebraic.Initial.fold_unique' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Algebraic.Initial.fold_unique

/-- info: 'Silmaril.Logic.Algebraic.Initial.fold_natural' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Algebraic.Initial.fold_natural

/-- info: 'Silmaril.Logic.Algebraic.Initial.closed_isInitial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Algebraic.Initial.closed_isInitial

/-- info: 'Silmaril.Logic.Algebraic.Initial.initialConstraint_sat_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Algebraic.Initial.initialConstraint_sat_iff

/-- info: 'Silmaril.Logic.Algebraic.Initial.fromEquational_modelExpansive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Algebraic.Initial.fromEquational_modelExpansive

/-- info: 'Silmaril.Logic.Algebraic.Initial.publicEquational_entails_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Algebraic.Initial.publicEquational_entails_iff

/-- info: 'Silmaril.Logic.Algebraic.Initial.Wasm.exec_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Algebraic.Initial.Wasm.exec_code

/-- info: 'Silmaril.Logic.Algebraic.Initial.Wasm.executes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Algebraic.Initial.Wasm.executes

/-- info: 'Silmaril.Logic.Algebraic.Initial.Examples.collapsed_rejects_constraint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Algebraic.Initial.Examples.collapsed_rejects_constraint

end Silmaril.Logic.Algebraic.Initial.Examples
