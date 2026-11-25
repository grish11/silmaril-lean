module

public import Silmaril.Languages.Python.Core.Refinement.Dynamic.Defs
import Silmaril.Languages.Python.Core.Refinement.Thms
import Silmaril.Languages.Python.Core.Thms
import Silmaril.Semantics.Operational.Maximal.Thms

public section

namespace Silmaril.Proofs.Languages.Python.Core.Refinement.Dynamic

open Silmaril.Languages.Python.Core
open Silmaril.Languages.Python.Core.Refinement (Observation expected FeatureLE arithmetic_supports)
open Silmaril.Languages.Python.Core.Refinement.Dynamic
open Silmaril.Semantics.Operational

variable {profile smaller larger : Profile} {expr : Expr} {op other : BinOp}
  {state : State} {body : Body} {obs : Observation}

theorem focus_unique (left : Focus expr op) (right : Focus expr other) : op = other := by
  induction left generalizing other with
  | compute =>
    cases right with
    | compute => rfl
    | left nested => cases nested
    | right nested => cases nested
  | left nested ih =>
    cases right with
    | compute => cases nested
    | left other => exact ih other
    | right _ => cases nested
  | right nested ih =>
    cases right with
    | compute => cases nested
    | left other => cases other
    | right other => exact ih other

theorem focus_of_step {next : Except Exception Expr} (step : expr.Step next) : ∃ op, Focus expr op := by
  induction step with
  | compute _ => exact ⟨_, .compute⟩
  | left _ ih =>
    obtain ⟨op, active⟩ := ih
    exact ⟨op, .left active⟩
  | right _ ih =>
    obtain ⟨op, active⟩ := ih
    exact ⟨op, .right active⟩

theorem focus_has_step (active : Focus expr op) : ∃ next, expr.Step next := by
  induction active with
  | compute =>
    exact ⟨_, .compute (BinOp.eval_iff.mp rfl)⟩
  | left _ ih =>
    obtain ⟨_, step⟩ := ih
    exact ⟨_, .left step⟩
  | right _ ih =>
    obtain ⟨_, step⟩ := ih
    exact ⟨_, .right step⟩

private theorem focus_supported (active : Focus expr op) (supported : profile.supports expr) :
    profile.allows op := by
  induction active with
  | compute =>
    simp only [Profile.supports, Bool.and_eq_true] at supported
    exact supported.1.1
  | left _ ih =>
    simp only [Profile.supports, Bool.and_eq_true] at supported
    exact ih supported.1.2
  | right _ ih =>
    simp only [Profile.supports, Bool.and_eq_true] at supported
    exact ih supported.2

private theorem allows_of_supported (supported : state.supported profile) : Allows profile state := by
  cases state with
  | returning expr => exact fun _ active => focus_supported active supported
  | raising _ | finished _ => trivial

private theorem allows_mono (features : FeatureLE smaller larger) (allows : Allows smaller state) :
    Allows larger state := by
  cases state with
  | returning expr => exact fun op active => features op (allows op active)
  | raising _ | finished _ => trivial

theorem runSem_toWithUB (profile : Profile) : (runSem profile).toWithUB = policy profile := by
  apply WithUB.Included.antisymm
  · exact ⟨⟨fun {_ _} ⟨label, guard, step⟩ => ⟨guard, label, step⟩, fun {_ _} h => h⟩, fun {_} h => h⟩
  · exact ⟨⟨fun {_ _} ⟨guard, label, step⟩ => ⟨label, guard, step⟩, fun {_ _} h => h⟩, fun {_} h => h⟩

theorem safeAt_iff :
    (runSem profile).toWithUB.SafeAt state ↔ ∀ ⦃last⦄, ordinary.Reach state last → Allows profile last := by
  rw [runSem_toWithUB]
  unfold policy
  exact WithUB.enforce_safe_iff.trans (and_iff_right (WithUB.ofOpSem_safe ordinary state))

theorem marked_iff_disabled :
    (runSem profile).ub (.returning expr) ↔ ∃ op, Focus expr op ∧ ¬ profile.allows op := by
  classical
  change (False ∨ ¬ ∀ op, Focus expr op → profile.allows op) ↔ _
  simp [not_forall, not_imp]

private theorem safe_of_supported (supported : state.supported profile) : (runSem profile).toWithUB.SafeAt state :=
  safeAt_iff.mpr fun {_} reach => allows_of_supported
    ((WithUB.enforce_safe_iff.mp (Silmaril.Languages.Python.Core.safe supported)).2 reach)

private theorem arithmetic_state (state : State) : state.supported .arithmetic := by
  cases state with
  | returning expr => exact arithmetic_supports expr
  | raising _ | finished _ => rfl

private theorem path_to_arithmetic {log : List Completion} {last : State}
    (path : (runSem profile).toLabelled.Path state log last) :
    (labelled .arithmetic).Path state log last := by
  induction path with
  | nil => exact .nil _
  | @silent source _ _ _ step _ ih => exact .silent ⟨arithmetic_state source, step.2⟩ ih
  | @visible source _ _ _ _ step _ ih => exact .visible ⟨arithmetic_state source, step.2⟩ ih

private theorem observed_eq (safe : (runSem profile).toWithUB.SafeAt body.start)
    (run : (runSem profile).Observes body.start obs) : obs = expected body := by
  classical
  cases obs with
  | diverges prefixes =>
    have infinite := ((runSem profile).diverges_iff body.start).mpr ⟨prefixes, run⟩
    exact (noDiverges .arithmetic body.start (infinite.map id fun source _ ⟨label, _, step⟩ =>
      ⟨arithmetic_state source, label, step⟩)).elim
  | finite log ending =>
    obtain ⟨last, path, endAt⟩ := run
    cases ending with
    | blocked => exact endAt.2.2.elim
    | stuck =>
      have reached := ((runSem profile).toLabelled.path_iff_reach body.start last).mp ⟨log, path⟩
      have permits : Allows profile last := by
        by_contra disabled
        exact safe ⟨last, reached, Or.inr disabled⟩
      rcases progress (arithmetic_state last) with ⟨label, target, step⟩ | observed
      · exact (endAt.1 target ⟨label, permits, step.2⟩).elim
      · exact (endAt.2.1 _ ⟨permits, observed.2⟩).elim
    | terminal outcome =>
      have finished : (labelled .arithmetic).Finishes body.start log outcome :=
        ⟨last, path_to_arithmetic path, arithmetic_state last, endAt.2.2⟩
      obtain ⟨rfl, rfl⟩ := (labelled_finishes_iff (arithmetic_supports body.value)).mp finished
      rfl

theorem observes_iff (safe : (runSem profile).toWithUB.SafeAt body.start) :
    (comparison profile).Observes body obs ↔ obs = expected body := by
  constructor
  · rintro ⟨start, entry, run⟩
    change start = body.start at entry
    exact observed_eq safe (entry ▸ run)
  · rintro rfl
    obtain ⟨seen, run⟩ := (runSem profile).exists_observation body.start
    exact ⟨body.start, rfl, observed_eq safe run ▸ run⟩

private theorem program_ub_iff :
    (comparison profile).toHasOpSem.UBReachable body ↔ (runSem profile).toWithUB.UBReachable body.start := by
  constructor
  · rintro ⟨start, entry, ub⟩
    change start = body.start at entry
    exact entry ▸ ub
  · exact fun ub => ⟨body.start, rfl, ub⟩

theorem behaviors_of_safe (safe : (runSem profile).toWithUB.SafeAt body.start) :
    behaviors profile body = {expected body} := by
  change (comparison profile).completed id body = _
  rw [HasRuns.completed_of_safe _ _ _ (fun ub => safe (program_ub_iff.mp ub))]
  ext observation
  change (∃ run, (comparison profile).Observes body run ∧ run = observation) ↔ observation = expected body
  exact ⟨fun ⟨_, run, eq⟩ => eq ▸ (observes_iff safe).mp run,
    fun eq => ⟨observation, (observes_iff safe).mpr eq, rfl⟩⟩

theorem behaviors_of_ub (ub : (runSem profile).toWithUB.UBReachable body.start) :
    behaviors profile body = Set.univ :=
  (comparison profile).completed_of_ub id body (program_ub_iff.mpr ub)

theorem safeAt_mono (features : FeatureLE smaller larger)
    (safe : (runSem smaller).toWithUB.SafeAt state) : (runSem larger).toWithUB.SafeAt state :=
  safeAt_iff.mpr fun {_} reached => allows_mono features (safeAt_iff.mp safe reached)

theorem behaviors_mono (features : FeatureLE smaller larger) : behaviors larger ≤ behaviors smaller := by
  intro body
  by_cases ub : (runSem smaller).toWithUB.UBReachable body.start
  · rw [behaviors_of_ub ub]
    exact Set.subset_univ _
  · rw [behaviors_of_safe (safeAt_mono features ub), behaviors_of_safe ub]

theorem improves_static (profile : Profile) :
    behaviors profile ≤ Silmaril.Languages.Python.Core.Refinement.behaviors profile := by
  intro body
  by_cases supported : profile.supports body.value
  · rw [behaviors_of_safe (safe_of_supported (state := body.start) supported),
      Silmaril.Languages.Python.Core.Refinement.behaviors_of_supported supported]
  · rw [Silmaril.Languages.Python.Core.Refinement.behaviors_of_unsupported supported]
    exact Set.subset_univ _

theorem lift_universal (features : FeatureLE smaller larger)
    (safe : (runSem smaller).toWithUB.SafeAt body.start) {Q : Observation → Prop}
    (holds : ∀ observed ∈ behaviors smaller body, Q observed) :
    (runSem larger).toWithUB.SafeAt body.start ∧
      (∃ observed, (comparison larger).Observes body observed) ∧
      ∀ observed, (comparison larger).Observes body observed → Q observed := by
  have safeLarger := safeAt_mono features safe
  exact ⟨safeLarger, ⟨expected body, (observes_iff safeLarger).mpr rfl⟩,
    fun obs run => holds obs (behaviors_mono features body (Or.inr ⟨obs, run, rfl⟩))⟩

end Silmaril.Proofs.Languages.Python.Core.Refinement.Dynamic
