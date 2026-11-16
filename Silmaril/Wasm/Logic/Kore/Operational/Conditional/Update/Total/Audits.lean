module

public import Silmaril.Wasm.Logic.Kore.Operational.Conditional.Update.Total.Examples
import Lean

open Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal.forced_infinite_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forced_infinite_hit

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal.forced_allEventually' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forced_allEventually

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal.entry_allEventually' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entry_allEventually

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal.entry_eventual_with_loop_divergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entry_eventual_with_loop_divergence

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal.source_entry_af' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_entry_af

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal.matching_iff_allEventually' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms matching_iff_allEventually

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal.source_entry_matching' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_entry_matching

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal.loop_allPartial_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms loop_allPartial_false

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal.loop_separates_partial_from_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms loop_separates_partial_from_total

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal.unreachable_not_allEventually' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms unreachable_not_allEventually

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal.stuck_not_allEventually' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stuck_not_allEventually

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal.Examples.concrete_progress_and_divergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Examples.concrete_progress_and_divergence

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal.Examples.concrete_source_matching' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Examples.concrete_source_matching

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal.Examples.empty_frame_no_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Examples.empty_frame_no_progress

-- Exact sets measured at a03beeab2944 by the strict Total.Audits target.
run_elab do
  let expected : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for declaration in #[
    ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal.forced_infinite_hit,
    ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal.forced_allEventually,
    ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal.entry_allEventually,
    ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal.entry_eventual_with_loop_divergence,
    ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal.source_entry_af,
    ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal.matching_iff_allEventually,
    ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal.source_entry_matching,
    ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal.loop_allPartial_false,
    ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal.loop_separates_partial_from_total,
    ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal.unreachable_not_allEventually,
    ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal.stuck_not_allEventually,
    ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal.Examples.concrete_progress_and_divergence,
    ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal.Examples.concrete_source_matching,
    ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal.Examples.empty_frame_no_progress
  ] do
    let actual ← Lean.collectAxioms declaration
    unless actual.size == expected.size && actual.all (fun ax => expected.contains ax) do
      throwError "Axiom set changed for {declaration}: {actual}; expected {expected}"
