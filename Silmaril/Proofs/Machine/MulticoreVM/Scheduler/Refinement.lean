module

public import Silmaril.Machine.MulticoreVM.Scheduler.Defs
public import Silmaril.Machine.MulticoreVM.Placed.Thms
public import Silmaril.Machine.MulticoreVM.Placed.StoreProjection.Defs

public section

namespace Silmaril.Proofs.Machine.MulticoreVM.Scheduler

open Silmaril.Machine.MulticoreVM
open Silmaril.Machine.MulticoreVM.Scheduler

universe u

variable {CoreId ThreadId Core Thread Choice Event : Type u} [DecidableEq CoreId]
variable {cores : CorePolicy CoreId ThreadId Core Thread}
variable {threads : ThreadPolicy CoreId ThreadId Core Thread}
variable {runnable : ThreadId → Thread → Prop} {life : Lifecycle ThreadId Thread Choice Event}
variable {instruction : Placed.Instruction CoreId ThreadId Core Thread Choice Event}
variable {State : Type u} {view : Placed.StoreView CoreId ThreadId Core Thread State}
variable {step : Transition State ThreadId Choice Event}
variable {initial next final : Config CoreId ThreadId Core Thread}
variable {core other : CoreId} {dispatch : Dispatch CoreId ThreadId} {thread resident : ThreadId}
variable {choice : Choice} {word : Placed.TaggedWord CoreId ThreadId Event}

theorem schedules_stores (h : threads.Schedules runnable core dispatch initial next) :
    next.cores = initial.cores ∧ next.threads = initial.threads := by
  cases h.2.2.2 with
  | idle changes | assign _ changes | migrate _ _ changes => exact ⟨changes.1, changes.2.1⟩
  | keep _ => exact ⟨rfl, rfl⟩

theorem schedules_ready (h : threads.Schedules runnable core dispatch initial next)
    (selected : dispatch.thread = some thread) :
    next.placement core = some thread ∧ Eligible runnable next.threads thread := by
  refine ⟨?_, (schedules_stores h).2 ▸ h.2.2.1 selected⟩
  cases h.2.2.2 with
  | idle _ => cases selected
  | keep atCore => cases selected; exact atCore
  | assign _ changes | migrate _ _ changes =>
    cases selected
    rw [changes.2.2, Function.update_self]

theorem schedules_toPlaced (h : threads.Schedules runnable core dispatch initial next) :
    Placed.Scheduled (life.instruction instruction) (dispatch.placedActions core) initial [] next := by
  cases h.2.2.2 with
  | idle changes => exact .cons (.idle h.2.1 changes) (.nil _)
  | keep _ => exact .nil _
  | assign waiting changes =>
    obtain ⟨_, allocated, _⟩ := h.2.2.1 rfl
    exact .cons (.assign h.2.1 (by rw [allocated]; rfl) waiting changes) (.nil _)
  | migrate atSource idle changes =>
    exact .cons (.migrate atSource idle h.2.1 changes) (.nil _)

theorem advance_effects (h : Advance life instruction core thread choice initial word next) :
    ∃ fragment, initial.placement core = some thread ∧
      life.instruction instruction core thread choice initial fragment next ∧
      word = Placed.tagFragment core thread fragment := by
  cases h with
  | execute atCore instr => exact ⟨_, atCore, instr, rfl⟩

theorem advance_machineStep (refines : instruction.RefinesBy view step)
    (h : Advance life instruction core thread choice initial word next) :
    machineStep step (view initial.cores initial.threads) (Placed.threadWord word)
      (view next.cores next.threads) := by
  obtain ⟨fragment, atCore, instr, rfl⟩ := advance_effects h
  exact ⟨thread, choice, fragment, refines atCore instr.2.1,
    Placed.threadWord_tagFragment core thread fragment⟩

theorem advance_blocked_releases (h : Advance life instruction core thread choice initial word next)
    (blocked : ¬ Eligible life.runnable next.threads thread) : next.placement core = none := by
  obtain ⟨_, _, instr, _⟩ := advance_effects h
  rw [instr.2.2.1 (Or.inr blocked), Function.update_self]

theorem advance_residence_origin (h : Advance life instruction core thread choice initial word next)
    (placed : next.placement other = some resident) : initial.placement other = some resident := by
  obtain ⟨fragment, _, instr, _⟩ := advance_effects h
  by_cases release : life.ReleasesSlot thread choice initial.threads fragment next.threads
  · rw [instr.2.2.1 release] at placed
    by_cases eq : other = core
    · subst other
      rw [Function.update_self] at placed
      cases placed
    · rwa [Function.update_of_ne eq] at placed
  · rwa [instr.2.2.2 release] at placed

variable {turn : Turn CoreId ThreadId Choice} {schedule : List (Turn CoreId ThreadId Choice)}

theorem round_placement_only
    (h : Round cores threads life instruction ⟨core, dispatch, none⟩ initial word next) :
    word = [] ∧ next.cores = initial.cores ∧ next.threads = initial.threads := by
  cases h with
  | place select place =>
    obtain rfl := select.2.2
    exact ⟨rfl, schedules_stores place⟩

theorem round_machineStep (refines : instruction.RefinesBy view step)
    (h : Round cores threads life instruction ⟨core, dispatch, some choice⟩ initial word next) :
    machineStep step (view initial.cores initial.threads) (Placed.threadWord word)
      (view next.cores next.threads) := by
  cases h with
  | execute select place _ advance =>
    rw [← select.2.2, ← (schedules_stores place).1, ← (schedules_stores place).2]
    exact advance_machineStep refines advance

private theorem placed_append {left right : Placed.Schedule CoreId ThreadId Choice}
    {tail : Placed.TaggedWord CoreId ThreadId Event}
    (first : Placed.Scheduled (life.instruction instruction) left initial word next)
    (rest : Placed.Scheduled (life.instruction instruction) right next tail final) :
    Placed.Scheduled (life.instruction instruction) (left ++ right) initial (word ++ tail) final := by
  induction first with
  | nil => exact rest
  | cons step _ ih => simpa only [List.cons_append, List.append_assoc] using .cons step (ih rest)

theorem round_toPlaced (h : Round cores threads life instruction turn initial word next) :
    Placed.Scheduled (life.instruction instruction) turn.placedActions initial word next := by
  cases h with
  | place select place =>
    obtain rfl := select.2.2
    simpa [Turn.placedActions] using schedules_toPlaced (life := life) (instruction := instruction) place
  | execute select place chosen advance =>
    obtain rfl := select.2.2
    simpa only [Turn.placedActions, chosen, List.nil_append, List.append_nil] using
      placed_append (schedules_toPlaced place) (.cons advance (.nil _))

theorem scheduled_toPlaced (h : Scheduled cores threads life instruction schedule initial word final) :
    Placed.Scheduled (life.instruction instruction) (schedule.flatMap Turn.placedActions) initial word final := by
  induction h with
  | nil => exact .nil _
  | cons round _ ih => exact placed_append (round_toPlaced round) ih

private theorem round_threadSchedule_length (h : Round cores threads life instruction turn initial word next) :
    (Placed.threadSchedule turn.placedActions).length = (if turn.choice.isSome then 1 else 0) := by
  cases h with
  | @place _ dispatch _ _ _ _ _ => cases dispatch <;> rfl
  | @execute _ dispatch _ _ _ _ _ _ _ _ _ chosen _ =>
    cases dispatch <;> cases chosen <;> rfl

theorem scheduled_threadSchedule_length (h : Scheduled cores threads life instruction schedule initial word final) :
    (threadSchedule schedule).length = (schedule.filter fun turn => turn.choice.isSome).length := by
  induction h with
  | nil => rfl
  | cons round _ ih =>
    have headLength := round_threadSchedule_length round
    simp only [threadSchedule, List.flatMap_cons, Placed.threadSchedule, List.filterMap_append,
      List.length_append, List.filter_cons] at ih headLength ⊢
    rw [headLength, ih]
    split <;> simp [Nat.add_comm]

end Silmaril.Proofs.Machine.MulticoreVM.Scheduler
