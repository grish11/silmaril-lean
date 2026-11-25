module

public import Silmaril.Courses.Cambridge.Concurrency.Mutex.ThreadLocal

/-! # Coincidence of global and thread-local semantics

Sewell, Theorem 27, pp. 94–96. Each direction follows by rule induction.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.Concurrency.Mutex

theorem Step.toLabelledStep {before after : Config} (step : Step before after) :
    LabelledStep before after := by
  induction step with
  | add l r s => exact ⟨.tau, .add l r, .tau s⟩
  | ge l r s => exact ⟨.tau, .ge l r, .tau s⟩
  | binaryLeft _ ih =>
      obtain ⟨action, localStep, effect⟩ := ih
      exact ⟨action, .binaryLeft localStep, effect⟩
  | binaryRight value _ ih =>
      obtain ⟨action, localStep, effect⟩ := ih
      exact ⟨action, .binaryRight value localStep, effect⟩
  | deref present => exact ⟨.read _ _, .deref _ _, .read present⟩
  | assignValue present => exact ⟨.write _ _, .assignValue _ _, .write present⟩
  | assignStep _ ih =>
      obtain ⟨action, localStep, effect⟩ := ih
      exact ⟨action, .assignStep localStep, effect⟩
  | seqSkip => exact ⟨.tau, .seqSkip _, .tau _⟩
  | seqStep _ ih =>
      obtain ⟨action, localStep, effect⟩ := ih
      exact ⟨action, .seqStep localStep, effect⟩
  | ifTrue => exact ⟨.tau, .ifTrue _ _, .tau _⟩
  | ifFalse => exact ⟨.tau, .ifFalse _ _, .tau _⟩
  | ifStep _ ih =>
      obtain ⟨action, localStep, effect⟩ := ih
      exact ⟨action, .ifStep localStep, effect⟩
  | «while» => exact ⟨.tau, .while _ _, .tau _⟩
  | parallelLeft _ ih =>
      obtain ⟨action, localStep, effect⟩ := ih
      exact ⟨action, .parallelLeft localStep, effect⟩
  | parallelRight _ ih =>
      obtain ⟨action, localStep, effect⟩ := ih
      exact ⟨action, .parallelRight localStep, effect⟩
  | lock available => exact ⟨.lock _, .lock _, .lock available⟩
  | unlock name s => exact ⟨.unlock name, .unlock name, .unlock name s⟩

theorem ThreadStep.toGlobalStep {e e' : Expr} {action : Action}
    (localStep : ThreadStep e action e') {s s' : SharedState} (effect : Effect action s s') :
    Step ⟨e, s⟩ ⟨e', s'⟩ := by
  induction localStep generalizing s s' with
  | add l r =>
      cases effect
      exact .add l r _
  | ge l r =>
      cases effect
      exact .ge l r _
  | binaryLeft _ ih => exact .binaryLeft (ih effect)
  | binaryRight value _ ih => exact .binaryRight value (ih effect)
  | deref =>
      cases effect with
      | read present => exact .deref present
  | assignValue =>
      cases effect with
      | write present => exact .assignValue present
  | assignStep _ ih => exact .assignStep (ih effect)
  | seqSkip =>
      cases effect
      exact .seqSkip
  | seqStep _ ih => exact .seqStep (ih effect)
  | ifTrue =>
      cases effect
      exact .ifTrue
  | ifFalse =>
      cases effect
      exact .ifFalse
  | ifStep _ ih => exact .ifStep (ih effect)
  | «while» =>
      cases effect
      exact .while
  | parallelLeft _ ih => exact .parallelLeft (ih effect)
  | parallelRight _ ih => exact .parallelRight (ih effect)
  | lock =>
      cases effect with
      | lock available => exact .lock available
  | unlock name =>
      cases effect
      exact .unlock name _

theorem LabelledStep.toStep {before after : Config} (step : LabelledStep before after) :
    Step before after := by
  obtain ⟨_, localStep, effect⟩ := step
  exact localStep.toGlobalStep effect

/-- Theorem 27 holds for every expression and pair of shared states. -/
theorem step_iff_labelledStep {before after : Config} : Step before after ↔ LabelledStep before after :=
  ⟨Step.toLabelledStep, LabelledStep.toStep⟩

end Silmaril.Courses.Cambridge.Concurrency.Mutex
