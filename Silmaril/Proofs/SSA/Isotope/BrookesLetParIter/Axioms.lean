module

import Silmaril.SSA.Isotope.BrookesLetParIter.Thms
import Silmaril.Proofs.SSA.Isotope.BrookesLetParIter.Regression
public meta import Lean.Elab.Command
meta import Lean.Util.CollectAxioms

/-! # Transitive axiom audit for the finite SC integration -/

open Lean Elab Command
open Silmaril.Isotope.BrookesLetParIter Silmaril.Isotope.BrookesLetParIter.Regression

namespace Silmaril.Proofs.SSA.Isotope.BrookesLetParIter

/-- Audit the public soundness and concrete observation declarations. -/
public meta def auditAxioms : CommandElabM Unit := do
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    ``instLawfulTypeModelSCType,
    ``instInstructionModelInstrSCTypeBoolM,
    ``pure_instruction_iff,
    ``Silmaril.Semantics.Brookes.Behavior.map_eq_mapResult,
    ``Silmaril.Semantics.Brookes.Behavior.parallelPairing,
    ``pairing,
    ``abort_empty,
    ``acquire_free,
    ``acquire_held,
    ``release_owner,
    ``release_nonowner,
    ``denote_readOnce,
    ``denote_program,
    ``program_completes,
    ``sound,
    ``interpret_sound,
    ``swap_program]
  let env ← getEnv
  for decl in declarations do
    unless env.contains decl do throwError "Missing audit declaration {decl}"
    let axioms ← collectAxioms decl
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{decl} transitively uses {axiomName}"
    logInfo m!"'{decl}' depends on axioms: {axioms.toList}"

run_cmd auditAxioms

end Silmaril.Proofs.SSA.Isotope.BrookesLetParIter
