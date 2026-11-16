module

public import Silmaril.Wasm.Logic.Kore.Operational.Conditional.Update.Source.Examples
import Lean

/-! Exact dependency sets measured by the successful targeted remote audit at
8ed2fadbf021. These guards cover source adequacy and the nonvacuity/domain controls. -/
/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.elaborate_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.elaborate_shape

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.elaborate_adequate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.elaborate_adequate

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.elaborate_to_matching' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.elaborate_to_matching

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.rawStep_of_elaborate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.rawStep_of_elaborate

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.rawStep_iff_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.rawStep_iff_step

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.raw_matching_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.raw_matching_sound

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.Examples.unsupported_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.Examples.unsupported_equality

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.Examples.wrong_sort_variable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.Examples.wrong_sort_variable

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.Examples.defined_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.Examples.defined_empty

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.Examples.capture_mismatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.Examples.capture_mismatch

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.Examples.claims_no_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.Examples.claims_no_step

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.Examples.actual_zero_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.Examples.actual_zero_bytes

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.Examples.actual_nonzero_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.Examples.actual_nonzero_bytes

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.Examples.val_declaration_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.Examples.val_declaration_checked

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.Examples.counter_declaration_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.Examples.counter_declaration_checked

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.Examples.nondeterministic_targets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.Examples.nondeterministic_targets


run_elab do
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  let selected := #[
    ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.elaborate_shape,
    ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.elaborate_adequate,
    ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.elaborate_to_matching,
    ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.rawStep_of_elaborate,
    ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.rawStep_iff_step,
    ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.raw_matching_sound,
    ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.Examples.unsupported_equality,
    ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.Examples.wrong_sort_variable,
    ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.Examples.defined_empty,
    ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.Examples.capture_mismatch,
    ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.Examples.claims_no_step,
    ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.Examples.actual_zero_bytes,
    ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.Examples.actual_nonzero_bytes,
    ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.Examples.val_declaration_checked,
    ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.Examples.counter_declaration_checked,
    ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.Examples.nondeterministic_targets]
  for declaration in selected do
    let actual ← Lean.collectAxioms declaration
    unless actual.size == expected.size && actual.all (fun ax => expected.contains ax) do
      throwError "Unexpected exact axiom dependency for {declaration}: {actual}"
