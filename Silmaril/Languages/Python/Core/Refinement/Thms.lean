module

public import Silmaril.Languages.Python.Core.Refinement.Defs
import Silmaril.Proofs.Languages.Python.Core.Refinement.Completion

public section

namespace Silmaril.Languages.Python.Core.Refinement

open Semantics.Operational

variable {smaller larger profile : Profile} {body : Body} {obs : Observation}

theorem supports_mono (features : FeatureLE smaller larger) {expr : Expr}
    (supported : smaller.supports expr) : larger.supports expr :=
  Proofs.Languages.Python.Core.Refinement.supports_mono features supported

theorem arithmetic_supports (expr : Expr) : Profile.arithmetic.supports expr :=
  Proofs.Languages.Python.Core.Refinement.arithmetic_supports expr

theorem runSem_toWithUB (profile : Profile) : (runSem profile).toWithUB = semantics profile :=
  Proofs.Languages.Python.Core.Refinement.runSem_toWithUB profile

theorem entry (profile : Profile) (body : Body) : (comparison profile).initial body body.start :=
  rfl

theorem ub_iff_unsupported :
    (comparison profile).toHasOpSem.UBReachable body ↔ ¬ profile.supports body.value :=
  Proofs.Languages.Python.Core.Refinement.ub_iff_unsupported

/-- Exhaustive maximal-run classification at an admitted body. The one
visible exit can report either a value or a Python exception. -/
theorem observes_iff (supported : profile.supports body.value) :
    (comparison profile).Observes body obs ↔ obs = expected body :=
  Proofs.Languages.Python.Core.Refinement.observes_iff supported

theorem behaviors_of_supported (supported : profile.supports body.value) :
    behaviors profile body = {expected body} :=
  Proofs.Languages.Python.Core.Refinement.behaviors_of_supported supported

theorem behaviors_of_unsupported (unsupported : ¬ profile.supports body.value) :
    behaviors profile body = Set.univ :=
  Proofs.Languages.Python.Core.Refinement.behaviors_of_unsupported unsupported

theorem coverage (features : FeatureLE smaller larger) (body : Body) :
    RunCoverage (comparison larger) (comparison smaller) id id body
      (fun source target => source = body.start ∧ target = body.start) :=
  Proofs.Languages.Python.Core.Refinement.coverage features body

/-- Feature inclusion reverses the order of completed behavior sets. -/
theorem behaviors_mono (features : FeatureLE smaller larger) :
    behaviors larger ≤ behaviors smaller :=
  Proofs.Languages.Python.Core.Refinement.behaviors_mono features

theorem arithmetic_lt_addition : behaviors .arithmetic < behaviors .addition :=
  Proofs.Languages.Python.Core.Refinement.arithmetic_lt_addition

/-- A universal property of the smaller profile's completed observations
lifts on a UB-free input. The stronger profile is also safe and has a
maximal run from its guaranteed entry. The view is identity. -/
theorem lift_universal (features : FeatureLE smaller larger)
    (safe : ¬ (comparison smaller).toHasOpSem.UBReachable body) {Q : Observation → Prop}
    (holds : ∀ observed ∈ behaviors smaller body, Q observed) :
    (¬ (comparison larger).toHasOpSem.UBReachable body) ∧
      (∃ observed, (comparison larger).Observes body observed) ∧
      ∀ observed, (comparison larger).Observes body observed → Q observed :=
  Proofs.Languages.Python.Core.Refinement.lift_universal features safe holds

end Silmaril.Languages.Python.Core.Refinement
