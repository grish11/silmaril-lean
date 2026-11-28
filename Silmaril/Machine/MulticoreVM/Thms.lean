module

public import Silmaril.Machine.MulticoreVM.Defs
import Silmaril.Proofs.Machine.MulticoreVM.Finite

public section

namespace Silmaril.Machine.MulticoreVM

open Silmaril.Semantics.ConcurrentTrace (Word Equivalent)

universe u

variable {State Thread Choice Event : Type u}
variable {step : Transition State Thread Choice Event}

/-- The named outcome of a monadic run has a schedule of exactly the same length. -/
theorem mem_run_iff_exists_schedule (n : Nat) {initial final : State} {word : Word Thread Event} :
    (final, word) ∈ namedOutcomes (run step n) initial ↔
      ∃ schedule : Schedule Thread Choice, schedule.length = n ∧
        Scheduled step schedule initial word final :=
  Proofs.Machine.MulticoreVM.mem_run_iff_exists_schedule n

/-- The nondeterministic run is the union over schedules, including each final state. -/
theorem run_eq_iUnion_scheduled (n : Nat) (initial : State) :
    namedOutcomes (run step n) initial =
      ⋃ schedule : {s : Schedule Thread Choice // s.length = n},
        scheduledOutcomes step schedule.val initial :=
  Proofs.Machine.MulticoreVM.run_eq_iUnion_scheduled n initial

/-- A quotient observation has an actual scheduled representative at that final state. -/
theorem mem_quotient_iff (n : Nat) (initial final : State)
    (word : Word Thread Event) :
    observeQuotient (final, word) ∈ observeQuotient '' namedOutcomes (run step n) initial ↔
      ∃ schedule : Schedule Thread Choice, schedule.length = n ∧
        ∃ actual, Scheduled step schedule initial actual final ∧ Equivalent actual word :=
  Proofs.Machine.MulticoreVM.mem_quotient_iff n initial final word

/-- Erasing scheduler decisions gives the existing finite machine trace relation. -/
theorem machineRuns_iff_exists_schedule {initial final : State} {word : Word Thread Event} :
    Silmaril.Machine.Trace.Runs (machineStep step) initial word final ↔
      ∃ schedule, Scheduled step schedule initial word final :=
  Proofs.Machine.MulticoreVM.machineRuns_iff_exists_schedule

/-- Successful execution of a deterministic step function realizes exactly its scheduled relation. -/
theorem execute_iff_scheduled
    (exec : Thread → Choice → State → Option (State × Fragment Thread Event))
    (schedule : Schedule Thread Choice) {initial final : State} {word : Word Thread Event} :
    execute exec schedule initial = some (final, word) ↔
      Scheduled (ofExecutor exec) schedule initial word final :=
  Proofs.Machine.MulticoreVM.execute_iff_scheduled exec schedule

end Silmaril.Machine.MulticoreVM
