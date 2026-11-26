module

public import Mathlib.SetTheory.Cardinal.NatCard
public import Silmaril.Machine.MulticoreVM.Placed.Defs
public import Silmaril.Machine.MulticoreVM.Thms
import Silmaril.Proofs.Machine.MulticoreVM.Placed.Refinement

public section

namespace Silmaril.Machine.MulticoreVM.Placed

open Silmaril.Semantics.ConcurrentTrace (Word)

universe u

variable {CoreId ThreadId Core Thread Choice Event : Type u}

/-- Each resident thread takes a slot on a present core. Thread IDs may be infinite. -/
theorem Config.resident_card_le_present [Finite CoreId] (cfg : Config CoreId ThreadId Core Thread) :
    Nat.card cfg.Resident ≤ Nat.card cfg.PresentCore :=
  Proofs.Machine.MulticoreVM.Placed.resident_card_le_present cfg

theorem Config.resident_card_le [Finite CoreId] (cfg : Config CoreId ThreadId Core Thread) :
    Nat.card cfg.Resident ≤ Nat.card CoreId :=
  cfg.resident_card_le_present.trans (Finite.card_subtype_le _)

@[simp] theorem threadWord_append (a b : TaggedWord CoreId ThreadId Event) :
    threadWord (a ++ b) = threadWord a ++ threadWord b := List.map_append

@[simp] theorem coreWord_append (a b : TaggedWord CoreId ThreadId Event) :
    coreWord (a ++ b) = coreWord a ++ coreWord b := List.map_append

@[simp] theorem threadWord_tagFragment (core : CoreId) (thread : ThreadId)
    (fragment : Fragment ThreadId Event) :
    threadWord (tagFragment core thread fragment) = nameFragment thread fragment :=
  Proofs.Machine.MulticoreVM.Placed.threadWord_tagFragment core thread fragment

@[simp] theorem coreWord_tagFragment (core : CoreId) (thread : ThreadId)
    (fragment : Fragment ThreadId Event) :
    coreWord (tagFragment core thread fragment) = fragment.map (fun
      | .event value => .event core (some value)
      | .sync _ => .event core none) :=
  Proofs.Machine.MulticoreVM.Placed.coreWord_tagFragment core thread fragment

/-- The abstract length counts instructions, including silent instructions. -/
theorem threadSchedule_length (schedule : Schedule CoreId ThreadId Choice) :
    (threadSchedule schedule).length = (schedule.filter fun a => a.threadDecision.isSome).length := by
  rw [threadSchedule, List.length_filterMap_eq_countP, List.countP_eq_length_filter]

theorem ofThreadStep_refines (step : Transition (ThreadId → Option Thread) ThreadId Choice Event) :
    (ofThreadStep (CoreId := CoreId) (Core := Core) step).Refines step :=
  fun {_ _ _ _ _ _} _ h => h.1

/-- Project a successful finite execution to a current-thread schedule, named word and final
thread store. Placement commands disappear, while even silent instructions take a step. -/
theorem Scheduled.refines [DecidableEq CoreId]
    {instruction : Instruction CoreId ThreadId Core Thread Choice Event}
    {step : Transition (ThreadId → Option Thread) ThreadId Choice Event}
    (refines : instruction.Refines step)
    {schedule : Schedule CoreId ThreadId Choice} {initial final : Config CoreId ThreadId Core Thread}
    {word : TaggedWord CoreId ThreadId Event} (run : Scheduled instruction schedule initial word final) :
    MulticoreVM.Scheduled step (threadSchedule schedule) initial.threads (threadWord word) final.threads :=
  Proofs.Machine.MulticoreVM.Placed.scheduled_refines refines run

/-- The projected named observation belongs to the abstract run at the filtered length. -/
theorem Scheduled.mem_threadRun [DecidableEq CoreId]
    {instruction : Instruction CoreId ThreadId Core Thread Choice Event}
    {step : Transition (ThreadId → Option Thread) ThreadId Choice Event}
    (refines : instruction.Refines step)
    {schedule : Schedule CoreId ThreadId Choice} {initial final : Config CoreId ThreadId Core Thread}
    {word : TaggedWord CoreId ThreadId Event} (run : Scheduled instruction schedule initial word final) :
    (final.threads, threadWord word) ∈ namedOutcomes
      (MulticoreVM.run step (schedule.filter fun a => a.threadDecision.isSome).length) initial.threads :=
  (mem_run_iff_exists_schedule _).mpr ⟨threadSchedule schedule, threadSchedule_length schedule,
    run.refines refines⟩

end Silmaril.Machine.MulticoreVM.Placed
