module

public import Silmaril.Wasm.Logic.Kore.Operational.Conditional.Update.ValueCompiler.Examples
import Lean

open Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.ValueCompiler
run_elab do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for declaration in #[``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.ValueCompiler.step_target,
      ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.ValueCompiler.write_agrees,
      ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.ValueCompiler.raw_step_af,
      ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.ValueCompiler.compileText_sound,
      ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.ValueCompiler.compileText_raw_af,
      ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.ValueCompiler.compileText_raw_matching,
      ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.ValueCompiler.Examples.checked_bytes,
      ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.ValueCompiler.Examples.compiled_bytes,
      ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.ValueCompiler.Examples.code_updates_guard,
      ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.ValueCompiler.Examples.raw_zero,
      ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.ValueCompiler.Examples.raw_nonzero,
      ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.ValueCompiler.Examples.actual_zero_af,
      ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.ValueCompiler.Examples.actual_nonzero_af,
      ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.ValueCompiler.Examples.zero_becomes_nonzero,
      ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.ValueCompiler.Examples.nonzero_becomes_zero,
      ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.ValueCompiler.Examples.wrong_value,
      ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.ValueCompiler.Examples.wrong_native_target,
      ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.ValueCompiler.Examples.wrong_target,
      ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.ValueCompiler.Examples.claims_rejected,
      ``Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.ValueCompiler.Examples.malformed_rejected] do
    for ax in (← Lean.collectAxioms declaration) do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {declaration}: {ax}"
