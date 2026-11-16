module

public import Silmaril.Logic.Matching.GuardedLFP.Boolean.Thms
public import Silmaril.Logic.FirstOrderLFP.Boolean.Examples

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GuardedLFP.Boolean.Examples
open Silmaril.Logic.Institution.Examples
open FirstOrderLFP.Reachability

/-- The compiled native complement of reachability agrees on an infinite model. -/
theorem native_nonreach :
    () ∈ (formula FirstOrderLFP.Boolean.Examples.notReaches).denote
      (expand (model Nat (fun a b => b = a + 1)).toStructure).base
      (fun i => some (![1, 0] i)) (fun i => i.elim0) :=
  (expanded_formula_denote (model Nat (fun a b => b = a + 1)) _ ![1, 0] ()).mpr FirstOrderLFP.Boolean.Examples.chain_nonreach

/-- A reachable captured target refutes the actual compiled negative claim. -/
theorem native_reachable_rejected :
    () ∉ (formula FirstOrderLFP.Boolean.Examples.notReaches).denote
      (expand (model Nat (fun a b => b = a + 1)).toStructure).base
      (fun i => some (![0, 5] i)) (fun i => i.elim0) := by
  intro h
  exact FirstOrderLFP.Boolean.Examples.chain_reachable_rejected
    ((expanded_formula_denote (model Nat (fun a b => b = a + 1)) _ ![0, 5] ()).mp h)

/-- The open theorem admits raw recursive sets containing inactive padding.
Complement conventions are therefore not restricted to canonical encoded sets. -/
theorem padded_negative_outer (M : Model FirstOrderLFP.Reachability.signature)
    (v : FirstOrderLFP.ObjEnv (decode M) (context 0))
    (η : FixedPoint.SetEnv (GuardedLFP.signature FirstOrderLFP.Reachability.signature).symbols M.base
      (setContext (FirstOrderLFP.Boolean.Examples.nullaryProfiles 1)))
    (w : M.base.carrier (.base .truth)) :
    w ∈ (formula FirstOrderLFP.Boolean.Examples.negativeOuter).denote M.base
      (fun i => (v i).val) η ↔
      (fun i => i.elim0) ∉ restrictEnv M (fun _ => false) η 0 :=
  (formula_denote M _ v η w).trans (FirstOrderLFP.Boolean.Examples.negativeOuter_denote _ _ v)

end Silmaril.Logic.Matching.GuardedLFP.Boolean.Examples

/-- info: 'Silmaril.Logic.FirstOrderLFP.Boolean.positiveWith_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.FirstOrderLFP.Boolean.positiveWith_denote

/-- info: 'Silmaril.Logic.FirstOrderLFP.Boolean.Formula.denote_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.FirstOrderLFP.Boolean.Formula.denote_map

/-- info: 'Silmaril.Logic.FirstOrderLFP.Boolean.institution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.FirstOrderLFP.Boolean.institution

/-- info: 'Silmaril.Logic.FirstOrderLFP.Boolean.fromPositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.FirstOrderLFP.Boolean.fromPositive

/-- info: 'Silmaril.Logic.FirstOrderLFP.Boolean.positive_entails_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.FirstOrderLFP.Boolean.positive_entails_iff

/-- info: 'Silmaril.Logic.FirstOrderLFP.Boolean.complement_lfp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.FirstOrderLFP.Boolean.complement_lfp

/-- info: 'Silmaril.Logic.Matching.GuardedLFP.Boolean.formula_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Matching.GuardedLFP.Boolean.formula_denote

/-- info: 'Silmaril.Logic.Matching.GuardedLFP.Boolean.formula_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Matching.GuardedLFP.Boolean.formula_map

/-- info: 'Silmaril.Logic.Matching.GuardedLFP.Boolean.formula_positiveWith' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Matching.GuardedLFP.Boolean.formula_positiveWith

/-- info: 'Silmaril.Logic.Matching.GuardedLFP.Boolean.lfpToGuardedMatching' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Matching.GuardedLFP.Boolean.lfpToGuardedMatching

/-- info: 'Silmaril.Logic.Matching.GuardedLFP.Boolean.lfp_sat_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Matching.GuardedLFP.Boolean.lfp_sat_iff

/-- info: 'Silmaril.Logic.Matching.GuardedLFP.Boolean.lfp_unsat_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Matching.GuardedLFP.Boolean.lfp_unsat_iff

/-- info: 'Silmaril.Logic.Matching.GuardedLFP.Boolean.lfp_entails_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Matching.GuardedLFP.Boolean.lfp_entails_iff

/-- info: 'Silmaril.Logic.FirstOrderLFP.Boolean.Examples.chain_nonreach' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.FirstOrderLFP.Boolean.Examples.chain_nonreach

/-- info: 'Silmaril.Logic.FirstOrderLFP.Boolean.Examples.negativeOuter_denote' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.FirstOrderLFP.Boolean.Examples.negativeOuter_denote

/-- info: 'Silmaril.Logic.FirstOrderLFP.Boolean.Examples.empty_nonexistence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.FirstOrderLFP.Boolean.Examples.empty_nonexistence

/-- info: 'Silmaril.Logic.Matching.GuardedLFP.Boolean.Examples.padded_negative_outer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Matching.GuardedLFP.Boolean.Examples.padded_negative_outer
