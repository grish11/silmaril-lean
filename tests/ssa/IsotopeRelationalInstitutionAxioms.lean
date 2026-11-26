module

import all tests.ssa.IsotopeRelationalInstitution
import all Silmaril.SSA.Isotope.Institution.Relational.Thms
import all Silmaril.SSA.Isotope.Institution.Relational.Inclusions.Defs
import all Silmaril.SSA.Isotope.Institution.Relational.Inclusions.Thms
import all Silmaril.SSA.Isotope.Institution.Relational.Model.Defs
import all Silmaril.SSA.Isotope.Institution.Relational.Model.Thms
import all Silmaril.SSA.Isotope.Institution.Relational.LetSeq.Defs
import all Silmaril.SSA.Isotope.Institution.Relational.LetSeq.Thms
import all Silmaril.SSA.Isotope.Institution.Relational.LetCase.Defs
import all Silmaril.SSA.Isotope.Institution.Relational.LetCase.Thms
import all Silmaril.SSA.Isotope.Institution.Relational.LetIter.Defs
import all Silmaril.SSA.Isotope.Institution.Relational.LetIter.Thms
import all Silmaril.Proofs.SSA.Isotope.Institution.Relational.Model
import all Silmaril.Proofs.SSA.Isotope.Institution.Relational.Inclusions
import all Silmaril.Proofs.SSA.Isotope.Institution.Relational.LetSeq
import all Silmaril.Proofs.SSA.Isotope.Institution.Relational.LetCase
import all Silmaril.Proofs.SSA.Isotope.Institution.Relational.LetIter
meta import Lean.Elab.Command
meta import Lean.Util.CollectAxioms

open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  let mut seen : NameSet := {}
  for (name, _) in env.constants do
    let some idx := env.getModuleIdxFor? name | continue
    let owner := env.header.moduleNames[idx.toNat]!
    unless (`Silmaril.SSA.Isotope.Institution.Relational).isPrefixOf owner ||
        (`Silmaril.Proofs.SSA.Isotope.Institution.Relational).isPrefixOf owner ||
        owner == `tests.ssa.IsotopeRelationalInstitution do
      continue
    for ax in (← collectAxioms name) do
      unless allowed.contains ax do
        throwError "{name} transitively uses {ax}"
      seen := seen.insert ax
    checked := checked + 1
  if checked == 0 then throwError "No relational institution declarations audited"
  logInfo m!"Audited {checked} declarations for transitive axioms: {seen.toList}"
