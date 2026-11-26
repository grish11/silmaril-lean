module

public import Silmaril.Machine.MulticoreVM.Placed.Outcomes.Defs
public import Silmaril.Machine.MulticoreVM.Placed.StoreProjection.Thms

public section

namespace Silmaril.Machine.MulticoreVM.Placed

universe u

variable {CoreId ThreadId Core Thread Choice Event : Type u}
variable {State : Type u}
variable {view : StoreView CoreId ThreadId Core Thread State}

/-- The direct projected trace and the quotient of the abstract named projection agree. -/
theorem observeThreadQuotient_eq (view : StoreView CoreId ThreadId Core Thread State)
    (outcome : TaggedOutcome CoreId ThreadId Core Thread Event) :
    observeThreadQuotient view outcome = MulticoreVM.observeQuotient (forgetCore view outcome) := rfl

/-- The two projection routes agree on any set of concrete outcomes. -/
theorem observeThreadQuotient_image (view : StoreView CoreId ThreadId Core Thread State)
    (outcomes : Set (TaggedOutcome CoreId ThreadId Core Thread Event)) :
    observeThreadQuotient view '' outcomes = MulticoreVM.observeQuotient '' (forgetCore view '' outcomes) :=
  (Set.image_image MulticoreVM.observeQuotient (forgetCore view) outcomes).symm

variable [DecidableEq CoreId]
variable {instruction : Instruction CoreId ThreadId Core Thread Choice Event}
variable {step : Transition State ThreadId Choice Event}

/-- Each projected named outcome is admitted by the projected abstract schedule. -/
theorem forgetCore_image_subset_scheduledOutcomes (refines : instruction.RefinesBy view step)
    (schedule : Schedule CoreId ThreadId Choice) (initial : Config CoreId ThreadId Core Thread) :
    forgetCore view '' taggedOutcomes instruction schedule initial ⊆
      MulticoreVM.scheduledOutcomes step (threadSchedule schedule) (view initial.cores initial.threads) := by
  rintro _ ⟨_, concrete, rfl⟩
  exact Scheduled.refinesBy refines concrete

/-- Each projected named outcome is admitted by the abstract runner at the filtered length. -/
theorem forgetCore_image_subset_namedOutcomes (refines : instruction.RefinesBy view step)
    (schedule : Schedule CoreId ThreadId Choice) (initial : Config CoreId ThreadId Core Thread) :
    forgetCore view '' taggedOutcomes instruction schedule initial ⊆
      namedOutcomes (MulticoreVM.run step (schedule.filter fun a => a.threadDecision.isSome).length)
        (view initial.cores initial.threads) := by
  rintro _ ⟨_, concrete, rfl⟩
  exact (mem_run_iff_exists_schedule _).mpr
    ⟨threadSchedule schedule, threadSchedule_length schedule, Scheduled.refinesBy refines concrete⟩

/-- Forward refinement on quotient outcomes for the projected schedule. -/
theorem observeThreadQuotient_image_subset_scheduledOutcomes (refines : instruction.RefinesBy view step)
    (schedule : Schedule CoreId ThreadId Choice) (initial : Config CoreId ThreadId Core Thread) :
    observeThreadQuotient view '' taggedOutcomes instruction schedule initial ⊆
      MulticoreVM.observeQuotient ''
        MulticoreVM.scheduledOutcomes step (threadSchedule schedule) (view initial.cores initial.threads) := by
  rw [observeThreadQuotient_image]
  exact Set.image_mono (forgetCore_image_subset_scheduledOutcomes refines schedule initial)

/-- Forward refinement on pairs of projected final states and concurrent thread traces. -/
theorem observeThreadQuotient_image_subset_run (refines : instruction.RefinesBy view step)
    (schedule : Schedule CoreId ThreadId Choice) (initial : Config CoreId ThreadId Core Thread) :
    observeThreadQuotient view '' taggedOutcomes instruction schedule initial ⊆
      MulticoreVM.observeQuotient ''
        namedOutcomes (MulticoreVM.run step (schedule.filter fun a => a.threadDecision.isSome).length)
          (view initial.cores initial.threads) := by
  rw [observeThreadQuotient_image]
  exact Set.image_mono (forgetCore_image_subset_namedOutcomes refines schedule initial)

end Silmaril.Machine.MulticoreVM.Placed
