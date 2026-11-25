module

public import Silmaril.Languages.Python.Core.Refinement.Dynamic.Defs
import Silmaril.Proofs.Languages.Python.Core.Refinement.Dynamic.Coverage

public section

namespace Silmaril.Languages.Python.Core.Refinement.Dynamic

open Semantics.Operational

variable {profile smaller larger : Profile} {expr : Expr} {op other : BinOp}
  {state : State} {body : Body} {obs : Observation}

theorem Focus.unique (left : Focus expr op) (right : Focus expr other) : op = other :=
  Proofs.Languages.Python.Core.Refinement.Dynamic.focus_unique left right

theorem Focus.of_step {next : Except Exception Expr} (step : expr.Step next) : ∃ op, Focus expr op :=
  Proofs.Languages.Python.Core.Refinement.Dynamic.focus_of_step step

theorem Focus.has_step (active : Focus expr op) : ∃ next, expr.Step next :=
  Proofs.Languages.Python.Core.Refinement.Dynamic.focus_has_step active

theorem runSem_toWithUB (profile : Profile) : (runSem profile).toWithUB = policy profile :=
  Proofs.Languages.Python.Core.Refinement.Dynamic.runSem_toWithUB profile

theorem marked_iff_disabled :
    (runSem profile).ub (.returning expr) ↔ ∃ op, Focus expr op ∧ ¬ profile.allows op :=
  Proofs.Languages.Python.Core.Refinement.Dynamic.marked_iff_disabled

theorem no_step_of_marked {label : Option Completion} {target : State}
    (marked : (runSem profile).ub state) : ¬ (runSem profile).step state label target :=
  fun step => marked.elim False.elim (fun disabled => disabled step.1)

/-- Safety holds exactly when every actually reachable Core state permits
its selected operation. Unvisited subexpressions impose no obligation. -/
theorem safeAt_iff :
    (runSem profile).toWithUB.SafeAt state ↔ ∀ ⦃last⦄, ordinary.Reach state last → Allows profile last :=
  Proofs.Languages.Python.Core.Refinement.Dynamic.safeAt_iff

theorem observes_iff (safe : (runSem profile).toWithUB.SafeAt body.start) :
    (comparison profile).Observes body obs ↔ obs = expected body :=
  Proofs.Languages.Python.Core.Refinement.Dynamic.observes_iff safe

theorem behaviors_of_safe (safe : (runSem profile).toWithUB.SafeAt body.start) :
    behaviors profile body = {expected body} :=
  Proofs.Languages.Python.Core.Refinement.Dynamic.behaviors_of_safe safe

theorem behaviors_of_ub (ub : (runSem profile).toWithUB.UBReachable body.start) :
    behaviors profile body = Set.univ :=
  Proofs.Languages.Python.Core.Refinement.Dynamic.behaviors_of_ub ub

theorem safeAt_mono (features : FeatureLE smaller larger)
    (safe : (runSem smaller).toWithUB.SafeAt state) : (runSem larger).toWithUB.SafeAt state :=
  Proofs.Languages.Python.Core.Refinement.Dynamic.safeAt_mono features safe

theorem behaviors_mono (features : FeatureLE smaller larger) : behaviors larger ≤ behaviors smaller :=
  Proofs.Languages.Python.Core.Refinement.Dynamic.behaviors_mono features

theorem improves_static (profile : Profile) : behaviors profile ≤ Refinement.behaviors profile :=
  Proofs.Languages.Python.Core.Refinement.Dynamic.improves_static profile

theorem lift_universal (features : FeatureLE smaller larger)
    (safe : (runSem smaller).toWithUB.SafeAt body.start) {Q : Observation → Prop}
    (holds : ∀ observed ∈ behaviors smaller body, Q observed) :
    (runSem larger).toWithUB.SafeAt body.start ∧
      (∃ observed, (comparison larger).Observes body observed) ∧
      ∀ observed, (comparison larger).Observes body observed → Q observed :=
  Proofs.Languages.Python.Core.Refinement.Dynamic.lift_universal features safe holds

end Silmaril.Languages.Python.Core.Refinement.Dynamic
