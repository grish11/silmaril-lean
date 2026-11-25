module

public import Silmaril.Languages.Python.Core.Refinement.Defs
import Silmaril.Languages.Python.Core.Thms
import Silmaril.Semantics.Operational.Maximal.Thms

public section

namespace Silmaril.Proofs.Languages.Python.Core.Refinement

open Silmaril.Languages.Python.Core Silmaril.Languages.Python.Core.Refinement
open Silmaril.Semantics.Operational

variable {smaller larger profile : Profile} {body : Body} {obs : Observation}

theorem supports_mono (features : FeatureLE smaller larger) {expr : Expr}
    (supported : smaller.supports expr) : larger.supports expr := by
  induction expr with
  | int _ => rfl
  | binary op left right ihLeft ihRight =>
    simp only [Profile.supports, Bool.and_eq_true] at supported ⊢
    exact ⟨⟨features op supported.1.1, ihLeft supported.1.2⟩, ihRight supported.2⟩

theorem arithmetic_supports (expr : Expr) : Profile.arithmetic.supports expr := by
  induction expr with
  | int _ => rfl
  | binary op left right ihLeft ihRight =>
    simp only [Profile.supports, Bool.and_eq_true]
    exact ⟨⟨by cases op <;> rfl, ihLeft⟩, ihRight⟩

theorem runSem_toWithUB (profile : Profile) : (runSem profile).toWithUB = semantics profile := by
  apply WithUB.Included.antisymm
  · exact ⟨⟨fun {_ _} ⟨label, guard, step⟩ => ⟨guard, label, step⟩, fun {_ _} h => h⟩, fun {_} h => h⟩
  · exact ⟨⟨fun {_ _} ⟨guard, label, step⟩ => ⟨label, guard, step⟩, fun {_ _} h => h⟩, fun {_} h => h⟩

theorem ub_iff_unsupported :
    (comparison profile).toHasOpSem.UBReachable body ↔ ¬ profile.supports body.value := by
  constructor
  · rintro ⟨s, entry, reached⟩ supported
    change s = body.start at entry
    subst s
    exact (Silmaril.Languages.Python.Core.safe (source := body.start) supported)
      (runSem_toWithUB profile ▸ reached)
  · intro unsupported
    exact ⟨body.start, rfl, body.start, .refl, Or.inr unsupported⟩

private theorem supported_of_path {last : State} {log : List Completion}
    (supported : profile.supports body.value) (path : (labelled profile).Path body.start log last) :
    last.supported profile := by
  classical
  by_contra unsupported
  have reach : (runSem profile).toWithUB.toOpSem.Reach body.start last :=
    ((labelled profile).path_iff_reach _ _).mp ⟨log, path⟩
  rw [runSem_toWithUB] at reach
  exact (Silmaril.Languages.Python.Core.safe (source := body.start) supported) ⟨last, reach, Or.inr unsupported⟩

private theorem observes_from_start (supported : profile.supports body.value) :
    (runSem profile).Observes body.start obs ↔ obs = expected body := by
  constructor
  · intro run
    cases obs with
    | diverges prefixes =>
      have infinite := ((runSem profile).diverges_iff body.start).mpr ⟨prefixes, run⟩
      rw [runSem_toWithUB] at infinite
      exact (noDiverges profile body.start infinite).elim
    | finite log ending =>
      obtain ⟨last, path, endAt⟩ := run
      cases ending with
      | blocked => exact endAt.2.2.elim
      | stuck =>
        rcases progress (supported_of_path supported path) with ⟨label, next, step⟩ | outcome
        · exact (endAt.1 next ⟨label, step⟩).elim
        · exact (endAt.2.1 _ outcome).elim
      | terminal outcome =>
        obtain ⟨rfl, rfl⟩ := (labelled_finishes_iff supported).mp ⟨last, path, endAt.2⟩
        rfl
  · rintro rfl
    obtain ⟨last, path, observed⟩ := (labelled_finishes_iff supported).mpr ⟨rfl, rfl⟩
    refine ⟨last, path, ?_, observed⟩
    rw [runSem_toWithUB]
    exact terminal profile observed

theorem observes_iff (supported : profile.supports body.value) :
    (comparison profile).Observes body obs ↔ obs = expected body := by
  constructor
  · rintro ⟨s, entry, observed⟩
    change s = body.start at entry
    exact (observes_from_start supported).mp (entry ▸ observed)
  · intro eq
    exact ⟨body.start, rfl, (observes_from_start supported).mpr eq⟩

theorem behaviors_of_supported (supported : profile.supports body.value) :
    behaviors profile body = {expected body} := by
  have safe : ¬ (comparison profile).toHasOpSem.UBReachable body :=
    fun ub => ub_iff_unsupported.mp ub supported
  change (comparison profile).completed id body = _
  rw [HasRuns.completed_of_safe _ _ _ safe]
  ext observation
  change (∃ run, (comparison profile).Observes body run ∧ run = observation) ↔ observation = expected body
  exact ⟨fun ⟨_, run, eq⟩ => eq ▸ (observes_iff supported).mp run,
    fun eq => ⟨observation, (observes_iff supported).mpr eq, rfl⟩⟩

theorem behaviors_of_unsupported (unsupported : ¬ profile.supports body.value) :
    behaviors profile body = Set.univ :=
  (comparison profile).completed_of_ub id body (ub_iff_unsupported.mpr unsupported)

theorem coverage (features : FeatureLE smaller larger) (body : Body) :
    RunCoverage (comparison larger) (comparison smaller) id id body
      (fun source target => source = body.start ∧ target = body.start) where
  entry {source} admitted := ⟨body.start, rfl, admitted, rfl⟩
  run {_ _ obs} related observed := by
    obtain ⟨rfl, rfl⟩ := related
    by_cases supported : smaller.supports body.value
    · have exactObs := (observes_from_start (supports_mono features supported)).mp observed
      exact Or.inr ⟨obs, (observes_from_start supported).mpr exactObs, rfl⟩
    · exact Or.inl ⟨body.start, .refl, Or.inr supported⟩

private theorem preserves_ub (features : FeatureLE smaller larger) :
    (comparison larger).toHasOpSem.UBReachable body → (comparison smaller).toHasOpSem.UBReachable body :=
  fun ub => ub_iff_unsupported.mpr (fun supported => ub_iff_unsupported.mp ub (supports_mono features supported))

theorem behaviors_mono (features : FeatureLE smaller larger) :
    behaviors larger ≤ behaviors smaller :=
  fun body => (coverage features body).completed_le (preserves_ub features)

/-- Division by zero has a defined exception in arithmetic. A successful
return of zero is an extra observation at the coarse addition boundary. -/
theorem arithmetic_lt_addition : behaviors .arithmetic < behaviors .addition := by
  have more : FeatureLE .addition .arithmetic := fun op _ => by cases op <;> rfl
  apply lt_of_le_not_ge (behaviors_mono more)
  intro reverse
  let division : Body := ⟨.binary .floorDiv (.int 1) (.int 0)⟩
  let spurious : Observation := .finite [.ok 0] (.terminal (.returned (.ok 0)))
  have permitted : spurious ∈ behaviors .addition division := by
    rw [behaviors_of_unsupported (profile := .addition) (body := division) (by decide)]
    exact Set.mem_univ _
  have impossible := reverse division permitted
  rw [behaviors_of_supported (arithmetic_supports division.value)] at impossible
  have wrong : spurious = expected division := impossible
  change (.finite [.ok 0] (.terminal (.returned (.ok 0))) : Observation) =
    .finite [.error .zeroDivisionError] (.terminal (.returned (.error .zeroDivisionError))) at wrong
  cases wrong

theorem lift_universal (features : FeatureLE smaller larger)
    (safe : ¬ (comparison smaller).toHasOpSem.UBReachable body) {Q : Observation → Prop}
    (holds : ∀ observed ∈ behaviors smaller body, Q observed) :
    (¬ (comparison larger).toHasOpSem.UBReachable body) ∧
      (∃ observed, (comparison larger).Observes body observed) ∧
      ∀ observed, (comparison larger).Observes body observed → Q observed := by
  obtain ⟨safeLarger, all⟩ := (coverage features body).safe_transfer (preserves_ub features) safe holds
  obtain ⟨observed, run⟩ := (runSem larger).exists_observation body.start
  exact ⟨safeLarger, ⟨observed, body.start, rfl, run⟩, all⟩

end Silmaril.Proofs.Languages.Python.Core.Refinement
