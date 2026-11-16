module

public import Silmaril.Logic.Rewriting.Examples
public import Silmaril.Wasm.Logic.Rewriting.Wasm

/-! Exact axiom dependencies for the main bridges and actual machine client. -/

/-- info: 'Silmaril.Logic.Rewriting.replacement' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Rewriting.replacement

/-- info: 'Silmaril.Logic.Rewriting.fromEquational_modelExpansive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Rewriting.fromEquational_modelExpansive

/-- info: 'Silmaril.Logic.Rewriting.toCanonicalReachability_modelExpansive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Rewriting.toCanonicalReachability_modelExpansive

/-- info: 'Silmaril.Logic.Rewriting.compile_satisfaction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Rewriting.compile_satisfaction

/-- info: 'Silmaril.Logic.Rewriting.Wasm.twoDrop_matching' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Rewriting.Wasm.twoDrop_matching
