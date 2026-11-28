module

public import Silmaril.Machine.MulticoreVM.Placed.StoreProjection.Defs
public import Silmaril.Machine.MulticoreVM.Placed.Thms
import Silmaril.Proofs.Machine.MulticoreVM.Placed.StoreProjection.Refinement

public section

namespace Silmaril.Machine.MulticoreVM.Placed

universe u

variable {CoreId ThreadId Core Thread Choice Event State : Type u}

/-- Use C8's schedule and word erasure with an abstract state that can read both stores. -/
theorem Scheduled.refinesBy [DecidableEq CoreId]
    {instruction : Instruction CoreId ThreadId Core Thread Choice Event}
    {view : StoreView CoreId ThreadId Core Thread State} {step : Transition State ThreadId Choice Event}
    (refines : instruction.RefinesBy view step)
    {schedule : Schedule CoreId ThreadId Choice} {initial final : Config CoreId ThreadId Core Thread}
    {word : TaggedWord CoreId ThreadId Event} (run : Scheduled instruction schedule initial word final) :
    MulticoreVM.Scheduled step (threadSchedule schedule) (view initial.cores initial.threads)
      (threadWord word) (view final.cores final.threads) :=
  Proofs.Machine.MulticoreVM.Placed.StoreProjection.scheduled_refinesBy refines run

end Silmaril.Machine.MulticoreVM.Placed
