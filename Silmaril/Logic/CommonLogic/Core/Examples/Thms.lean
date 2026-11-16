module

public import Silmaril.Logic.CommonLogic.Core.Examples.Defs

@[expose] public section

namespace Silmaril.Logic.CommonLogic.Core.Examples

theorem higher_predicate_holds : (room signature).Sat model higherPredicate := by
  refine ⟨(1 : Nat), ?_⟩
  change ([1] : List Nat) ≠ []
  decide

theorem sequence_witness_holds : (room signature).Sat model sequenceWitness := by
  refine ⟨([8,9] : List Nat), ?_⟩
  change 4 = 4
  rfl

theorem marker_splicing :
    (Expr.append (.marker ()) (.marker ()) : Expr signature 0 0 .sequence).eval
      model Fin.elim0 Fin.elim0 = ([2,3,2,3] : List Nat) := rfl

theorem every_sequence_nonempty_false : ¬ (room signature).Sat model everySequenceNonempty := by
  intro h
  exact h [] rfl

theorem computed_head_holds : (room signature).Sat model computedHead := by
  change ([1] : List Nat) ≠ []
  decide

theorem name_not_nullary_holds : (room signature).Sat model nameNotNullary := by
  change ¬ (1 : Nat) = 0
  decide

theorem nondiscourse_outside : ∀ x, model.embed x ≠ model.nondiscourse () :=
  model.outside ()

theorem renamed_name_not_nullary_false :
    ¬ (room signature).Sat model (nameNotNullary.map collapse) := by
  change ¬ ¬ (0 : Nat) = 0
  exact fun h => h rfl

theorem reduct_name_not_nullary_false :
    ¬ (room signature).Sat ((Model.reduct collapse).obj model) nameNotNullary :=
  fun h => renamed_name_not_nullary_false ((Formula.holds_map collapse model _ _ nameNotNullary).mpr h)

/-- info: 'Silmaril.Logic.CommonLogic.Core.Examples.higher_predicate_holds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms higher_predicate_holds
/-- info: 'Silmaril.Logic.CommonLogic.Core.Examples.sequence_witness_holds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sequence_witness_holds
/-- info: 'Silmaril.Logic.CommonLogic.Core.Examples.every_sequence_nonempty_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms every_sequence_nonempty_false

end Silmaril.Logic.CommonLogic.Core.Examples
