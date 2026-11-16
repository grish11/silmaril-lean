module

public import Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source.SemanticExamples
public import Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source.Claim.Audits
import Lean

namespace Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source.Audits
open Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites
open Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source
open Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source.SemanticExamples

-- Check transitive proof dependencies, including the actual parsed examples.
run_elab do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for declaration in #[``derivation_sound, ``package_installed_source,
      ``package_installed_is_axiom, ``package_installed_source_with_scope,
      ``branch_checked, ``branch_raw_step_iff, ``branch_derivation,
      ``branch_all_partial, ``rightComplete, ``initial_not_post,
      ``branch_installed_origins, ``cannot_ignore_right, ``empty_checked,
      ``empty_not_well_defined, ``empty_no_successor, ``guards_checked,
      ``checked_equality_guard_false, ``checked_membership_guard_true,
      ``equality_native_lhs_disabled, ``membership_native_lhs_enabled] do
    for ax in (← Lean.collectAxioms declaration) do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {declaration}: {ax}"

end Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source.Audits
