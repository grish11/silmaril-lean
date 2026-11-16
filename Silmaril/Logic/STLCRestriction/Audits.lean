module

public import Silmaril.Logic.STLCRestriction.Examples

/-! Exact axiom allowlists for the model-restriction bridge and actual controls. -/

/-- info: 'Silmaril.Logic.STLCRestriction.toInhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.STLCRestriction.toInhabited
/-- info: 'Silmaril.Logic.STLCRestriction.forget_naturality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.STLCRestriction.forget_naturality
/-- info: 'Silmaril.Logic.STLCRestriction.expansion_iff' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.STLCRestriction.expansion_iff
/-- info: 'Silmaril.Logic.STLCRestriction.modelExpansive_iff_isEmpty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.STLCRestriction.modelExpansive_iff_isEmpty
/-- info: 'Silmaril.Logic.STLCRestriction.not_modelExpansive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.STLCRestriction.not_modelExpansive
/-- info: 'Silmaril.Logic.STLCRestriction.matching_modelExpansive_iff_isEmpty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.STLCRestriction.matching_modelExpansive_iff_isEmpty
/-- info: 'Silmaril.Logic.STLCRestriction.entails_preserved' depends on axioms: [propext, Classical.choice] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.STLCRestriction.entails_preserved
/-- info: 'Silmaril.Logic.STLCRestriction.sat_iff_inhabited_source' depends on axioms: [propext, Classical.choice] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.STLCRestriction.sat_iff_inhabited_source
/-- info: 'Silmaril.Logic.STLCRestriction.unsat_preserved' depends on axioms: [propext, Classical.choice] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.STLCRestriction.unsat_preserved
/-- info: 'Silmaril.Logic.STLCRestriction.matching_satisfaction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.STLCRestriction.matching_satisfaction
/-- info: 'Silmaril.Logic.STLCRestriction.matching_entails_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.STLCRestriction.matching_entails_preserved
/-- info: 'Silmaril.Logic.STLCRestriction.matching_sat_reduces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.STLCRestriction.matching_sat_reduces
/-- info: 'Silmaril.Logic.STLCRestriction.matching_unsat_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.STLCRestriction.matching_unsat_preserved
/-- info: 'Silmaril.Logic.STLCRestriction.Examples.collapse_satisfaction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.STLCRestriction.Examples.collapse_satisfaction
/-- info: 'Silmaril.Logic.STLCRestriction.Examples.beta_compiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.STLCRestriction.Examples.beta_compiled
/-- info: 'Silmaril.Logic.STLCRestriction.Examples.bad_typing_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.STLCRestriction.Examples.bad_typing_rejected
/-- info: 'Silmaril.Logic.STLCRestriction.Examples.empty_unit_no_expansion' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.STLCRestriction.Examples.empty_unit_no_expansion
