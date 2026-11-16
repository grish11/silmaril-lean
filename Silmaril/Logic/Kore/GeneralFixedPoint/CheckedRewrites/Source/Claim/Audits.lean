module

public import Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source.Claim.Thms
public import Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source.ParsedExamples
public import Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source.CaptureExamples
import Lean

namespace Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source.Claim.Audits
open Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source

-- Check transitive dependencies of the claim bridge and its concrete semantic controls.
run_elab do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for declaration in #[
      ``history_checked_owner,
      ``checkRewrite_original,
      ``ClaimSelection.checked_owner,
      ``ClaimSelection.source,
      ``ClaimSelection.original_operands,
      ``ClaimSelection.meaning,
      ``ClaimSelection.native_adequate,
      ``ClaimSelection.StepObligations,
      ``ClaimSelection.step,
      ``ClaimSelection.step_sound,
      ``ParsedExamples.accepted,
      ``ParsedExamples.source_positions,
      ``ParsedExamples.same_rules,
      ``ParsedExamples.good_pre,
      ``ParsedExamples.good_post,
      ``ParsedExamples.bad_pre,
      ``ParsedExamples.bad_post,
      ``ParsedExamples.good_obligations,
      ``ParsedExamples.good_derivation,
      ``ParsedExamples.good_sound,
      ``ParsedExamples.positive_initial,
      ``ParsedExamples.parsedComplete,
      ``ParsedExamples.bad_no_obligations,
      ``ParsedExamples.bad_complete_avoids,
      ``ParsedExamples.bad_not_all_partial,
      ``ParsedExamples.bad_no_closed_derivation,
      ``CaptureExamples.accepted,
      ``CaptureExamples.actual_captures,
      ``CaptureExamples.actual_guard,
      ``CaptureExamples.incoherent_rejected,
      ``CaptureExamples.wrong_endpoint_rejected] do
    for ax in (← Lean.collectAxioms declaration) do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {declaration}: {ax}"

end Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source.Claim.Audits
