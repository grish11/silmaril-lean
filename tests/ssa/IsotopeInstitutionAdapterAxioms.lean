module

import all tests.ssa.IsotopeInstitutionAdapters
import all Silmaril.SSA.Isotope.Institution.Adapters.Thms
import all Silmaril.Proofs.SSA.Isotope.Institution.Adapters.Hierarchy
import all Silmaril.SSA.Isotope.Institution.Adapters.Powerset.Defs
import all Silmaril.SSA.Isotope.Institution.Adapters.Powerset.Thms
import all Silmaril.SSA.Isotope.Institution.Adapters.Iteration.Defs
import all Silmaril.SSA.Isotope.Institution.Adapters.Iteration.Thms
import all Silmaril.Proofs.SSA.Isotope.Institution.Adapters.Powerset
import all Silmaril.Proofs.SSA.Isotope.Institution.Adapters.Iteration
meta import Lean.Elab.Command
meta import Lean.Util.CollectAxioms

open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in env.constants do
    let some idx := env.getModuleIdxFor? name | continue
    let owner := env.header.moduleNames[idx.toNat]!
    unless (`Silmaril.SSA.Isotope.Institution.Adapters).isPrefixOf owner ||
        (`Silmaril.Proofs.SSA.Isotope.Institution.Adapters).isPrefixOf owner ||
        owner == `tests.ssa.IsotopeInstitutionAdapters do
      continue
    for ax in (← collectAxioms name) do
      unless allowed.contains ax do
        throwError "{name} transitively uses {ax}"
    checked := checked + 1
  if checked == 0 then throwError "No adapter declarations audited"
  logInfo m!"Audited {checked} adapter and fixture declarations for transitive axioms"
