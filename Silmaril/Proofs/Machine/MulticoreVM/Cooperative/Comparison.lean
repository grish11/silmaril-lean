module

public import Silmaril.Machine.MulticoreVM.Cooperative.Defs
public import Silmaril.Machine.MulticoreVM.Thms

public section

namespace Silmaril.Proofs.Machine.MulticoreVM.Cooperative

open Silmaril.Machine.MulticoreVM
open Silmaril.Machine.MulticoreVM.Cooperative
open Silmaril.Semantics.ConcurrentTrace (Word)

universe u

variable {State Thread Choice Event Abstract : Type u}
variable {program : Program State Thread Choice Event} {policy : DispatchPolicy State Thread}
variable {view : State → Abstract} {abstractStep : Transition Abstract Thread Choice Event}
variable {step : Transition State Thread Choice Event}

theorem scheduled_refines (refines : program.Refines view abstractStep)
    {moves : Schedule Thread (Action Choice)} {initial final : Config State Thread}
    {word : Word Thread Event} (path : Scheduled (Step program policy) moves initial word final) :
    Scheduled abstractStep (atomicSchedule moves) (view initial.vm) word (view final.vm) := by
  induction path with
  | nil cfg => exact .nil (view cfg.vm)
  | @cons decision schedule initial next final fragment tail first _ ih =>
    cases decision with
    | mk thread action =>
      cases first with
      | dispatch => exact ih
      | atomic _ atomic => exact .cons (refines.atomic atomic) ih
      | yield _ didYield => exact refines.yield_preserves didYield ▸ ih
      | complete => exact ih

theorem everyAtomic_refines (step : Transition State Thread Choice Event) :
    (everyAtomic step).Refines Prod.fst step where
  atomic h := h.2.2
  yield_preserves := by
    intro _ state next h
    have same : next = (state.1, false) := h.2
    rw [same]

theorem atomicSchedule_instrument (schedule : Schedule Thread Choice) :
    atomicSchedule (instrument schedule) = schedule := by
  induction schedule with
  | nil => rfl
  | cons decision schedule ih =>
    cases decision with
    | mk thread choice => exact congrArg (List.cons ⟨thread, choice⟩) ih

theorem scheduled_instrument {schedule : Schedule Thread Choice} {initial final : State}
    {word : Word Thread Event} (path : Scheduled step schedule initial word final) :
    Scheduled (Step (everyAtomic step) anyDispatch) (instrument schedule)
      (Config.start (initial, false)) word (Config.start (final, false)) := by
  induction path with
  | nil state => exact .nil (Config.start (state, false))
  | @cons decision schedule initial next final fragment tail first _ ih =>
    have ready : (everyAtomic step).Runnable decision.thread (initial, false) :=
      ⟨id, Or.inl ⟨decision.choice, fragment, (next, true), rfl, rfl, first⟩⟩
    exact .cons (decision := ⟨decision.thread, .dispatch⟩) (.dispatch trivial ready)
      (.cons (decision := ⟨decision.thread, .atomic decision.choice⟩)
        (.atomic (fragment := fragment) (next := (next, true)) id ⟨rfl, rfl, first⟩)
        (.cons (decision := ⟨decision.thread, .yield⟩)
          (.yield (state := (next, true)) id ⟨rfl, rfl⟩) ih))

theorem observedOutcomes_everyAtomic (step : Transition State Thread Choice Event)
    (initial : State) (n : Nat) :
    observedOutcomes (everyAtomic step) anyDispatch Prod.fst (Config.start (initial, false)) n =
      namedOutcomes (run step n) initial := by
  ext ⟨final, word⟩
  rw [mem_run_iff_exists_schedule]
  constructor
  · rintro ⟨moves, target, len, path, rfl⟩
    exact ⟨atomicSchedule moves, len, scheduled_refines (everyAtomic_refines step) path⟩
  · rintro ⟨schedule, len, path⟩
    exact ⟨instrument schedule, Config.start (final, false),
      (congrArg List.length (atomicSchedule_instrument schedule)).trans len,
      scheduled_instrument path, rfl⟩

end Silmaril.Proofs.Machine.MulticoreVM.Cooperative
