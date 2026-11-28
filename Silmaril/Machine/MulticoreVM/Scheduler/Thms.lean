module

public import Silmaril.Machine.MulticoreVM.Scheduler.Defs
public import Silmaril.Machine.MulticoreVM.Placed.StoreProjection.Thms
import Silmaril.Proofs.Machine.MulticoreVM.Scheduler.Refinement

public section

namespace Silmaril.Machine.MulticoreVM.Scheduler

universe u

variable {CoreId ThreadId Core Thread Choice Event : Type u}
variable {cores : CorePolicy CoreId ThreadId Core Thread}
variable {threads : ThreadPolicy CoreId ThreadId Core Thread}
variable {runnable : ThreadId → Thread → Prop} {life : Lifecycle ThreadId Thread Choice Event}
variable {instruction : Placed.Instruction CoreId ThreadId Core Thread Choice Event}
variable {State : Type u} {view : Placed.StoreView CoreId ThreadId Core Thread State}
variable {step : Transition State ThreadId Choice Event}
variable {initial next final : Config CoreId ThreadId Core Thread}
variable {core other : CoreId} {dispatch : Dispatch CoreId ThreadId} {thread resident : ThreadId}
variable {choice : Choice} {word : Placed.TaggedWord CoreId ThreadId Event}

/-- An opportunity can be granted to any policy-approved present core, without a state change. -/
theorem CorePolicy.selects_iff :
    cores.Selects initial core next ↔ cores initial core ∧ (initial.cores core).isSome ∧ next = initial :=
  Iff.rfl

variable [DecidableEq CoreId]

/-- Scheduling alone preserves both stores. -/
theorem ThreadPolicy.Schedules.stores (h : threads.Schedules runnable core dispatch initial next) :
    next.cores = initial.cores ∧ next.threads = initial.threads :=
  Proofs.Machine.MulticoreVM.Scheduler.schedules_stores h

/-- A dispatched thread is resident and runnable on the selected core. -/
theorem ThreadPolicy.Schedules.ready (h : threads.Schedules runnable core dispatch initial next)
    (selected : dispatch.thread = some thread) :
    next.placement core = some thread ∧ Eligible runnable next.threads thread :=
  Proofs.Machine.MulticoreVM.Scheduler.schedules_ready h selected

/-- Dispatch is realized by silent C8 placement commands. Keeping the resident uses no command. -/
theorem ThreadPolicy.Schedules.toPlaced (h : threads.Schedules runnable core dispatch initial next) :
    Placed.Scheduled (life.instruction instruction) (dispatch.placedActions core) initial [] next :=
  Proofs.Machine.MulticoreVM.Scheduler.schedules_toPlaced h

theorem Lifecycle.instruction_refinesBy (life : Lifecycle ThreadId Thread Choice Event)
    (refines : instruction.RefinesBy view step) : (life.instruction instruction).RefinesBy view step :=
  fun {_ _ _ _ _ _} atCore h => refines atCore h.2.1

/-- An advance has a resident executor and an instruction outcome with the stated lifecycle effects. -/
theorem Advance.effects (h : Advance life instruction core thread choice initial word next) :
    ∃ fragment, initial.placement core = some thread ∧
      life.instruction instruction core thread choice initial fragment next ∧
      word = Placed.tagFragment core thread fragment :=
  Proofs.Machine.MulticoreVM.Scheduler.advance_effects h

/-- Even a silent advance gives one abstract machine step. -/
theorem Advance.machineStep (refines : instruction.RefinesBy view step)
    (h : Advance life instruction core thread choice initial word next) :
    MulticoreVM.machineStep step (view initial.cores initial.threads) (Placed.threadWord word)
      (view next.cores next.threads) :=
  Proofs.Machine.MulticoreVM.Scheduler.advance_machineStep refines h

theorem Advance.blocked_releases (h : Advance life instruction core thread choice initial word next)
    (blocked : ¬ Eligible life.runnable next.threads thread) : next.placement core = none :=
  Proofs.Machine.MulticoreVM.Scheduler.advance_blocked_releases h blocked

/-- An instruction can release its own slot. Any resulting residence was already present. -/
theorem Advance.residence_origin (h : Advance life instruction core thread choice initial word next)
    (placed : next.placement other = some resident) : initial.placement other = some resident :=
  Proofs.Machine.MulticoreVM.Scheduler.advance_residence_origin h placed

/-- A previously unplaced thread can become runnable without gaining a slot. -/
theorem Advance.eligible_waiter (h : Advance life instruction core thread choice initial word next)
    (waiting : ∀ c, initial.placement c ≠ some resident)
    (eligible : Eligible life.runnable next.threads resident) :
    Eligible life.runnable next.threads resident ∧ ∀ c, next.placement c ≠ some resident :=
  ⟨eligible, fun c atCore => waiting c (h.residence_origin atCore)⟩

/-- Without an advance, a round contributes only placement and has no abstract observation. -/
theorem Round.placement_only
    (h : Round cores threads life instruction ⟨core, dispatch, none⟩ initial word next) :
    word = [] ∧ next.cores = initial.cores ∧ next.threads = initial.threads :=
  Proofs.Machine.MulticoreVM.Scheduler.round_placement_only h

/-- An executing round refines one abstract machine step from the pre-scheduling store. -/
theorem Round.machineStep (refines : instruction.RefinesBy view step)
    (h : Round cores threads life instruction ⟨core, dispatch, some choice⟩ initial word next) :
    MulticoreVM.machineStep step (view initial.cores initial.threads) (Placed.threadWord word)
      (view next.cores next.threads) :=
  Proofs.Machine.MulticoreVM.Scheduler.round_machineStep refines h

variable {turn : Turn CoreId ThreadId Choice} {schedule : List (Turn CoreId ThreadId Choice)}

theorem Round.toPlaced (h : Round cores threads life instruction turn initial word next) :
    Placed.Scheduled (life.instruction instruction) turn.placedActions initial word next :=
  Proofs.Machine.MulticoreVM.Scheduler.round_toPlaced h

theorem Scheduled.toPlaced (h : Scheduled cores threads life instruction schedule initial word final) :
    Placed.Scheduled (life.instruction instruction) (schedule.flatMap Turn.placedActions) initial word final :=
  Proofs.Machine.MulticoreVM.Scheduler.scheduled_toPlaced h

/-- Erase placement and core names, preserving the instruction schedule, named word and observed state. -/
theorem Scheduled.refines (refines : instruction.RefinesBy view step)
    (h : Scheduled cores threads life instruction schedule initial word final) :
    MulticoreVM.Scheduled step (threadSchedule schedule) (view initial.cores initial.threads)
      (Placed.threadWord word) (view final.cores final.threads) :=
  h.toPlaced.refinesBy (life.instruction_refinesBy refines)

theorem Scheduled.threadSchedule_length (h : Scheduled cores threads life instruction schedule initial word final) :
    (threadSchedule schedule).length = (schedule.filter fun turn => turn.choice.isSome).length :=
  Proofs.Machine.MulticoreVM.Scheduler.scheduled_threadSchedule_length h

/-- The abstract run length counts advances, including those with empty instruction fragments. -/
theorem Scheduled.mem_threadRun (refines : instruction.RefinesBy view step)
    (h : Scheduled cores threads life instruction schedule initial word final) :
    (view final.cores final.threads, Placed.threadWord word) ∈ MulticoreVM.namedOutcomes
      (MulticoreVM.run step (schedule.filter fun turn => turn.choice.isSome).length)
      (view initial.cores initial.threads) :=
  (MulticoreVM.mem_run_iff_exists_schedule _).mpr ⟨_, h.threadSchedule_length, h.refines refines⟩

end Silmaril.Machine.MulticoreVM.Scheduler
