module

import Silmaril.Languages.Python.Core.Refinement.Dynamic.Thms
import Silmaril.Languages.Python.Core.Refinement.Thms
import Silmaril.Languages.Python.Core.Thms

/-! # Python Core comparisons at the first unsupported operation -/

open Silmaril.Languages.Python.Core Silmaril.Languages.Python.Core.Refinement.Dynamic
open Silmaril.Languages.Python.Core.Refinement (Observation)
open Silmaril.Semantics.Operational

private def delayed : Body :=
  ⟨.binary .floorDiv (.binary .add (.int 1) (.int 2)) (.int 3)⟩

private def divisionState : State := .returning (.binary .floorDiv (.int 3) (.int 3))

private theorem firstStep : (runSem .addition).step delayed.start none divisionState := by
  constructor
  · intro op active
    have eq : op = .add := active.unique (.left .compute)
    subst op
    rfl
  · exact .expr (.left (.compute (.add 1 2)))

private theorem divisionMarked : (runSem .addition).ub divisionState :=
  marked_iff_disabled.mpr ⟨.floorDiv, .compute, by decide⟩

example : ¬ (runSem .addition).ub delayed.start :=
  fun marked => marked.elim False.elim (fun disabled => disabled firstStep.1)

example (label : Option Completion) (target : State) : ¬ (runSem .addition).step divisionState label target :=
  no_step_of_marked divisionMarked

example : behaviors .addition delayed = Set.univ :=
  behaviors_of_ub ⟨divisionState, .single ⟨none, firstStep⟩, divisionMarked⟩

private def divisionOnly : Profile := ⟨false, true⟩

private def earlyError : Body :=
  ⟨.binary .floorDiv (.binary .floorDiv (.int 1) (.int 0)) (.binary .add (.int 2) (.int 5))⟩

private def zeroError : Observation :=
  .finite [.error .zeroDivisionError] (.terminal (.returned (.error .zeroDivisionError)))

private theorem safeBefore {profile : Profile} {source target : State} {label : Option Completion}
    (step : Step source label target) (allows : Allows profile source)
    (safe : (runSem profile).toWithUB.SafeAt target) :
    (runSem profile).toWithUB.SafeAt source := by
  apply safeAt_iff.mpr
  intro last reach
  rcases reach.cases_head with same | ⟨_, ⟨_, first⟩, rest⟩
  · exact same ▸ allows
  · exact safeAt_iff.mp safe ((first.deterministic step).2 ▸ rest)

private theorem safeFinished (result : Completion) :
    (runSem divisionOnly).toWithUB.SafeAt (.finished result) := by
  apply safeAt_iff.mpr
  intro last reach
  rcases reach.cases_head with rfl | ⟨_, ⟨_, first⟩, _⟩
  · trivial
  · cases first

private theorem earlyErrorSafe : (runSem divisionOnly).toWithUB.SafeAt earlyError.start := by
  apply safeBefore (.expr (.left (.compute (.divZero 1))))
  · intro op active
    have eq : op = .floorDiv := active.unique (.left .compute)
    subst op
    rfl
  · exact safeBefore (.raise .zeroDivisionError) trivial (safeFinished _)

example : behaviors divisionOnly earlyError = {zeroError} := behaviors_of_safe earlyErrorSafe

example : (comparison divisionOnly).Observes earlyError zeroError := (observes_iff earlyErrorSafe).mpr rfl

example : Silmaril.Languages.Python.Core.Refinement.behaviors divisionOnly earlyError = Set.univ :=
  Silmaril.Languages.Python.Core.Refinement.behaviors_of_unsupported (by decide)

example :
    (∃ obs, (comparison .arithmetic).Observes earlyError obs) ∧
    ∀ obs, (comparison .arithmetic).Observes earlyError obs → obs = zeroError := by
  have features : Silmaril.Languages.Python.Core.Refinement.FeatureLE divisionOnly .arithmetic :=
    fun op _ => by cases op <;> rfl
  exact (lift_universal features earlyErrorSafe (Q := (· = zeroError)) fun obs seen => by
    rwa [behaviors_of_safe earlyErrorSafe] at seen).2
