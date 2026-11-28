module

public import Silmaril.Machine.MulticoreVM.Synchronized.Physical.Defs
public import Silmaril.Machine.MulticoreVM.Scheduler.Thms
import Silmaril.Proofs.Machine.MulticoreVM.Synchronized.Physical

public section

namespace Silmaril.Machine.MulticoreVM.Synchronized.Physical

variable {CoreId : Type} [DecidableEq CoreId] {memoryCore : CoreId}
variable {cores : Scheduler.CorePolicy CoreId ThreadId Shared Slot}
variable {threads : Scheduler.ThreadPolicy CoreId ThreadId Shared Slot}
variable {schedule : List (Scheduler.Turn CoreId ThreadId Choice)}
variable {initial final : Config CoreId} {word : Placed.TaggedWord CoreId ThreadId Event}

theorem instruction_refines (memoryCore : CoreId) :
    (instruction memoryCore).RefinesBy (view memoryCore) step :=
  Proofs.Machine.MulticoreVM.Synchronized.Physical.instruction_refines memoryCore

/-- Physical execution projects to the enlarged current-thread VM, including its
shared words, synchronization events, and participant lists. -/
theorem Scheduled.refines (execution : Scheduled memoryCore cores threads schedule initial word final) :
    MulticoreVM.Scheduled step (Scheduler.threadSchedule schedule)
      (view memoryCore initial.cores initial.threads) (Placed.threadWord word)
      (view memoryCore final.cores final.threads) :=
  Scheduler.Scheduled.refines (instruction_refines memoryCore) execution

/-- Every instruction counts toward the abstract length. A scheduling-only round
does not contribute to that length or to the named word. -/
theorem Scheduled.mem_threadRun (execution : Scheduled memoryCore cores threads schedule initial word final) :
    (view memoryCore final.cores final.threads, Placed.threadWord word) ∈
      namedOutcomes (run step (schedule.filter fun turn => turn.choice.isSome).length)
        (view memoryCore initial.cores initial.threads) :=
  Scheduler.Scheduled.mem_threadRun (instruction_refines memoryCore) execution

end Silmaril.Machine.MulticoreVM.Synchronized.Physical
