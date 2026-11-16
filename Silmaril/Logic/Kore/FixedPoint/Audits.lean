module

public import Silmaril.Logic.Kore.FixedPoint.Controls

/-! Declaration-level axiom reports for semantic adequacy and source controls. -/
/-- info: 'Silmaril.Proofs.Logic.Kore.FixedPoint.elaborate_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.FixedPoint.Semantics.elaborate_sound

/-- info: 'Silmaril.Logic.Kore.FixedPoint.Semantics.read_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.FixedPoint.Semantics.read_sound

/-- info: 'Silmaril.Logic.Kore.FixedPoint.Semantics.accepted_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.FixedPoint.Semantics.accepted_monotone

/-- info: 'Silmaril.Logic.Kore.FixedPoint.Semantics.closed_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.FixedPoint.Semantics.closed_satisfies

/-- info: 'Silmaril.Logic.Kore.FixedPoint.Examples.read_reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.FixedPoint.Examples.read_reaches

/-- info: 'Silmaril.Logic.Kore.FixedPoint.Examples.read_forever' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.FixedPoint.Examples.read_forever

/-- info: 'Silmaril.Logic.Kore.FixedPoint.Examples.source_reaches_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.FixedPoint.Examples.source_reaches_all

/-- info: 'Silmaril.Logic.Kore.FixedPoint.Examples.source_forever_loop_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.FixedPoint.Examples.source_forever_loop_only

/-- info: 'Silmaril.Logic.Kore.FixedPoint.Examples.identity_least' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.FixedPoint.Examples.identity_least

/-- info: 'Silmaril.Logic.Kore.FixedPoint.Examples.identity_greatest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.FixedPoint.Examples.identity_greatest

/-- info: 'Silmaril.Logic.Kore.FixedPoint.Examples.shadow_universe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.FixedPoint.Examples.shadow_universe

/-- info: 'Silmaril.Logic.Kore.FixedPoint.Examples.read_shadow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.FixedPoint.Examples.read_shadow

/-- info: 'Silmaril.Logic.Kore.FixedPoint.Examples.negative_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.FixedPoint.Examples.negative_rejected

/-- info: 'Silmaril.Logic.Kore.FixedPoint.Examples.wrong_binder_sort_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.FixedPoint.Examples.wrong_binder_sort_rejected

/-- info: 'Silmaril.Logic.Kore.FixedPoint.Examples.nearest_wrong_sort_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.FixedPoint.Examples.nearest_wrong_sort_rejected

/-- info: 'Silmaril.Logic.Kore.FixedPoint.Examples.unknown_set_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.FixedPoint.Examples.unknown_set_rejected

/-- info: 'Silmaril.Logic.Kore.FixedPoint.Examples.unknown_symbol_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.FixedPoint.Examples.unknown_symbol_rejected

/-- info: 'Silmaril.Logic.Kore.FixedPoint.Examples.malformed_set_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.FixedPoint.Examples.malformed_set_rejected

/-- info: 'Silmaril.Logic.Kore.FixedPoint.Examples.wrong_arity_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.FixedPoint.Examples.wrong_arity_rejected

/-- info: 'Silmaril.Logic.Kore.FixedPoint.Examples.unsupported_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.FixedPoint.Examples.unsupported_rejected

/-- info: 'Silmaril.Logic.Kore.FixedPoint.Examples.trailing_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.FixedPoint.Examples.trailing_rejected

/-- info: 'Silmaril.Logic.Kore.FixedPoint.Examples.separate_namespaces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.FixedPoint.Examples.separate_namespaces

/-- info: 'Silmaril.Logic.Kore.FixedPoint.Examples.mixed_quantifier_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.FixedPoint.Examples.mixed_quantifier_accepted

/-- info: 'Silmaril.Logic.Kore.FixedPoint.Examples.source_shadow_universe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.FixedPoint.Examples.source_shadow_universe

/-- info: 'Silmaril.Logic.Kore.FixedPoint.Examples.read_identity_least' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.FixedPoint.Examples.read_identity_least

/-- info: 'Silmaril.Logic.Kore.FixedPoint.Examples.read_identity_greatest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.FixedPoint.Examples.read_identity_greatest

/-- info: 'Silmaril.Logic.Kore.FixedPoint.Examples.binary_symbol_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.FixedPoint.Examples.binary_symbol_accepted
