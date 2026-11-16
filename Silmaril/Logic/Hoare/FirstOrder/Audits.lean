module

public import Silmaril.Logic.Hoare.FirstOrder.Examples

/-! Exact allowlists for the structural compiler, model corridor and concrete controls. -/

/-- info: 'Silmaril.Logic.Hoare.FirstOrder.toHoare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Hoare.FirstOrder.toHoare
/-- info: 'Silmaril.Logic.Hoare.FirstOrder.compile_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Hoare.FirstOrder.compile_correct
/-- info: 'Silmaril.Logic.Hoare.FirstOrder.closed_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Hoare.FirstOrder.closed_correct
/-- info: 'Silmaril.Logic.Hoare.FirstOrder.sentence_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Hoare.FirstOrder.sentence_correct
/-- info: 'Silmaril.Logic.Hoare.FirstOrder.native_reduct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Hoare.FirstOrder.native_reduct
/-- info: 'Silmaril.Logic.Hoare.FirstOrder.compile_naturality' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Hoare.FirstOrder.compile_naturality
/-- info: 'Silmaril.Logic.Hoare.FirstOrder.sentence_naturality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Hoare.FirstOrder.sentence_naturality
/-- info: 'Silmaril.Logic.Hoare.FirstOrder.modelReduct_natural' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Hoare.FirstOrder.modelReduct_natural
/-- info: 'Silmaril.Logic.Hoare.FirstOrder.toHoare_modelExpansive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Hoare.FirstOrder.toHoare_modelExpansive
/-- info: 'Silmaril.Logic.Hoare.FirstOrder.entails_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Hoare.FirstOrder.entails_iff
/-- info: 'Silmaril.Logic.Hoare.FirstOrder.sat_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Hoare.FirstOrder.sat_iff
/-- info: 'Silmaril.Logic.Hoare.FirstOrder.unsat_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Hoare.FirstOrder.unsat_iff
/-- info: 'Silmaril.Logic.Hoare.FirstOrder.Examples.empty_havoc' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Hoare.FirstOrder.Examples.empty_havoc
/-- info: 'Silmaril.Logic.Hoare.FirstOrder.Examples.empty_allFalse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Hoare.FirstOrder.Examples.empty_allFalse
/-- info: 'Silmaril.Logic.Hoare.FirstOrder.Examples.empty_not_existsTrue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Hoare.FirstOrder.Examples.empty_not_existsTrue
/-- info: 'Silmaril.Logic.Hoare.FirstOrder.Examples.bool_not_collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Hoare.FirstOrder.Examples.bool_not_collapse
/-- info: 'Silmaril.Logic.Hoare.FirstOrder.Examples.open_equality_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Hoare.FirstOrder.Examples.open_equality_rejected
/-- info: 'Silmaril.Logic.Hoare.FirstOrder.Examples.unused_store_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Hoare.FirstOrder.Examples.unused_store_closed
/-- info: 'Silmaril.Logic.Hoare.FirstOrder.Examples.badBinders_rejected' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Hoare.FirstOrder.Examples.badBinders_rejected
/-- info: 'Silmaril.Logic.Hoare.FirstOrder.Examples.unrestricted_reflexive_failure' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Hoare.FirstOrder.Examples.unrestricted_reflexive_failure
/-- info: 'Silmaril.Logic.Hoare.FirstOrder.Examples.actual_model_arrow' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Hoare.FirstOrder.Examples.actual_model_arrow
/-- info: 'Silmaril.Logic.Hoare.FirstOrder.Examples.actual_reduct_square' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Hoare.FirstOrder.Examples.actual_reduct_square
/-- info: 'Silmaril.Logic.Hoare.FirstOrder.Examples.admitted_sorts_fixed' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Hoare.FirstOrder.Examples.admitted_sorts_fixed
/-- info: 'Silmaril.Logic.Hoare.FirstOrder.Examples.actual_relation_observation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Hoare.FirstOrder.Examples.actual_relation_observation
/-- info: 'Silmaril.Logic.Hoare.FirstOrder.Examples.actual_relation_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Hoare.FirstOrder.Examples.actual_relation_rejected
/-- info: 'Silmaril.Logic.Hoare.FirstOrder.Examples.havoc_does_not_preserve_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Hoare.FirstOrder.Examples.havoc_does_not_preserve_equality
/-- info: 'Silmaril.Logic.Hoare.FirstOrder.Examples.nested_reflexive_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Hoare.FirstOrder.Examples.nested_reflexive_valid
