module

public import Silmaril.Machine.MulticoreVM.Cooperative.Defs
public import Silmaril.Machine.MulticoreVM.Thms
import Silmaril.Proofs.Machine.MulticoreVM.Cooperative.Comparison

public section

namespace Silmaril.Machine.MulticoreVM.Cooperative

open Silmaril.Semantics.ConcurrentTrace (Word)

universe u

variable {State Thread Choice Event Abstract : Type u}
variable {program : Program State Thread Choice Event} {policy : DispatchPolicy State Thread}
variable {view : State → Abstract} {abstractStep : Transition Abstract Thread Choice Event}
variable {step : Transition State Thread Choice Event}

/-- A finite cooperative run projects to a valid arbitrary atomic schedule with the same
chronological word and the projected endpoint states. The supplied dispatch policy can
restrict the cooperative run. The abstract scheduler is unrestricted. -/
theorem scheduled_refines (refines : program.Refines view abstractStep)
    {moves : Schedule Thread (Action Choice)} {initial final : Config State Thread}
    {word : Word Thread Event} (path : Scheduled (Step program policy) moves initial word final) :
    Scheduled abstractStep (atomicSchedule moves) (view initial.vm) word (view final.vm) :=
  Proofs.Machine.MulticoreVM.Cooperative.scheduled_refines refines path

theorem everyAtomic_refines (step : Transition State Thread Choice Event) :
    (everyAtomic step).Refines Prod.fst step :=
  Proofs.Machine.MulticoreVM.Cooperative.everyAtomic_refines step

theorem atomicSchedule_instrument (schedule : Schedule Thread Choice) :
    atomicSchedule (instrument schedule) = schedule :=
  Proofs.Machine.MulticoreVM.Cooperative.atomicSchedule_instrument schedule

/-- Every successful finite atomic schedule has a cooperative lift under unrestricted
dispatch. The lift starts idle and ends idle, even when the last atomic step is terminal. -/
theorem scheduled_instrument {schedule : Schedule Thread Choice} {initial final : State}
    {word : Word Thread Event} (path : Scheduled step schedule initial word final) :
    Scheduled (Step (everyAtomic step) anyDispatch) (instrument schedule)
      (Config.start (initial, false)) word (Config.start (final, false)) :=
  Proofs.Machine.MulticoreVM.Cooperative.scheduled_instrument path

/-- The instrumented cooperative VM and the arbitrary scheduler have exactly the same
finite outcomes, indexed by atomic steps and observed at the underlying VM state. -/
theorem observedOutcomes_everyAtomic (step : Transition State Thread Choice Event)
    (initial : State) (n : Nat) :
    observedOutcomes (everyAtomic step) anyDispatch Prod.fst (Config.start (initial, false)) n =
      namedOutcomes (run step n) initial :=
  Proofs.Machine.MulticoreVM.Cooperative.observedOutcomes_everyAtomic step initial n

end Silmaril.Machine.MulticoreVM.Cooperative
