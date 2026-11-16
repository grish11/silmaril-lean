module

public import Silmaril.Logic.Algebraic.Lambda.Examples

@[expose] public section
namespace Silmaril.Logic.Algebraic.Lambda

/-- info: 'Silmaril.Logic.Algebraic.Lambda.eval_term' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_term
/-- info: 'Silmaril.Logic.Algebraic.Lambda.satisfies_equation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms satisfies_equation
/-- info: 'Silmaril.Logic.Algebraic.Lambda.reduct_expand' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reduct_expand
/-- info: 'Silmaril.Logic.Algebraic.Lambda.term_naturality' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms term_naturality
/-- info: 'Silmaril.Logic.Algebraic.Lambda.toSTLC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms toSTLC
/-- info: 'Silmaril.Logic.Algebraic.Lambda.toSTLC_modelExpansive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms toSTLC_modelExpansive
/-- info: 'Silmaril.Logic.Algebraic.Lambda.entails_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entails_iff
/-- info: 'Silmaril.Logic.Algebraic.Lambda.sat_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sat_iff
/-- info: 'Silmaril.Logic.Algebraic.Lambda.Examples.empty_base_preserved' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Examples.empty_base_preserved
/-- info: 'Silmaril.Logic.Algebraic.Lambda.Examples.false_equation_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Examples.false_equation_rejected

end Silmaril.Logic.Algebraic.Lambda
