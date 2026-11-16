module

public import Silmaril.Logic.Algebraic.OrderSorted.Initial.Examples
public import Silmaril.Logic.Algebraic.OrderSorted.Free
public import Silmaril.Logic.Algebraic.OrderSorted.Initial

/-- info: 'Silmaril.Logic.Algebraic.OrderSorted.Free.coerce_injective' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Algebraic.OrderSorted.Free.coerce_injective

/-- info: 'Silmaril.Logic.Algebraic.OrderSorted.Free.model' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Algebraic.OrderSorted.Free.model

/-- info: 'Silmaril.Logic.Algebraic.OrderSorted.Free.foldHom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Algebraic.OrderSorted.Free.foldHom

/-- info: 'Silmaril.Logic.Algebraic.OrderSorted.Free.fold_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Algebraic.OrderSorted.Free.fold_unique

/-- info: 'Silmaril.Logic.Algebraic.OrderSorted.Free.freeHomEquiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Algebraic.OrderSorted.Free.freeHomEquiv

/-- info: 'Silmaril.Logic.Algebraic.OrderSorted.Free.fold_natural' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Algebraic.OrderSorted.Free.fold_natural

/-- info: 'Silmaril.Logic.Algebraic.OrderSorted.Free.closed_isInitial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Algebraic.OrderSorted.Free.closed_isInitial

/-- info: 'Silmaril.Logic.Algebraic.OrderSorted.Initial.emptyReductHomUnique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Algebraic.OrderSorted.Initial.emptyReductHomUnique

/-- info: 'Silmaril.Logic.Algebraic.OrderSorted.Initial.freeAt_iff_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Algebraic.OrderSorted.Initial.freeAt_iff_initial

/-- info: 'Silmaril.Logic.Algebraic.OrderSorted.Initial.initialConstraint_sat_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Algebraic.OrderSorted.Initial.initialConstraint_sat_iff

/-- info: 'Silmaril.Logic.Algebraic.OrderSorted.Initial.closedModel_isInitial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Algebraic.OrderSorted.Initial.closedModel_isInitial

/-- info: 'Silmaril.Logic.Algebraic.OrderSorted.Initial.closedModel_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Algebraic.OrderSorted.Initial.closedModel_satisfies

/-- info: 'Silmaril.Logic.Algebraic.OrderSorted.Initial.fromOrderSorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Algebraic.OrderSorted.Initial.fromOrderSorted

/-- info: 'Silmaril.Logic.Algebraic.OrderSorted.Initial.fromOrderSorted_modelExpansive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Algebraic.OrderSorted.Initial.fromOrderSorted_modelExpansive

/-- info: 'Silmaril.Logic.Algebraic.OrderSorted.Initial.original_entails_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Algebraic.OrderSorted.Initial.original_entails_iff

/-- info: 'Silmaril.Logic.Algebraic.OrderSorted.Initial.Examples.proper_coercion_image' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Algebraic.OrderSorted.Initial.Examples.proper_coercion_image

/-- info: 'Silmaril.Logic.Algebraic.OrderSorted.Initial.Examples.distinct_free_values' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Algebraic.OrderSorted.Initial.Examples.distinct_free_values

/-- info: 'Silmaril.Logic.Algebraic.OrderSorted.Initial.Examples.numericCollapse_not_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Algebraic.OrderSorted.Initial.Examples.numericCollapse_not_injective

/-- info: 'Silmaril.Logic.Algebraic.OrderSorted.Initial.Examples.no_collapsed_hom' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Algebraic.OrderSorted.Initial.Examples.no_collapsed_hom

/-- info: 'Silmaril.Logic.Algebraic.OrderSorted.Initial.Examples.collapsed_not_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Algebraic.OrderSorted.Initial.Examples.collapsed_not_initial

/-- info: 'Silmaril.Logic.Algebraic.OrderSorted.Initial.Examples.collapsed_fails_constraint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Algebraic.OrderSorted.Initial.Examples.collapsed_fails_constraint

/-- info: 'Silmaril.Logic.Algebraic.OrderSorted.Initial.Examples.free_lower_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Algebraic.OrderSorted.Initial.Examples.free_lower_empty

/-- info: 'Silmaril.Logic.Algebraic.OrderSorted.Initial.Examples.free_upper_inhabited' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Algebraic.OrderSorted.Initial.Examples.free_upper_inhabited

/-- info: 'Silmaril.Logic.Algebraic.OrderSorted.Initial.Examples.actual_initial_constraint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Algebraic.OrderSorted.Initial.Examples.actual_initial_constraint
