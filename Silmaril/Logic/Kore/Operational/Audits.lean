module

public import Silmaril.Logic.Kore.Operational.Examples

/-! Exact axiom allowlists for the concrete operational frontend. -/

/-- info: 'Silmaril.Logic.Kore.Operational.compile_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Kore.Operational.compile_denote
/-- info: 'Silmaril.Logic.Kore.Operational.next_compile_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Kore.Operational.next_compile_denote
/-- info: 'Silmaril.Logic.Kore.Operational.nextSentence_satisfies_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Kore.Operational.nextSentence_satisfies_iff
/-- info: 'Silmaril.Logic.Kore.Operational.compile_satisfies_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Kore.Operational.compile_satisfies_iff
/-- info: 'Silmaril.Logic.Kore.Operational.compiled_matching_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Kore.Operational.compiled_matching_sound
/-- info: 'Silmaril.Logic.Kore.Operational.Examples.alias_tree_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Kore.Operational.Examples.alias_tree_correspondence
/-- info: 'Silmaril.Logic.Kore.Operational.Examples.source_tree_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Kore.Operational.Examples.source_tree_correspondence
/-- info: 'Silmaril.Logic.Kore.Operational.Examples.source_step_exact' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Kore.Operational.Examples.source_step_exact
/-- info: 'Silmaril.Logic.Kore.Operational.Examples.emitted_matching_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Kore.Operational.Examples.emitted_matching_valid
/-- info: 'Silmaril.Logic.Kore.Operational.Examples.no_step_without_axioms' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Kore.Operational.Examples.no_step_without_axioms
