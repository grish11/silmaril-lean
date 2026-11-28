module

public import Silmaril.Machine.MulticoreVM.Swaps.Defs
import Silmaril.Proofs.Machine.MulticoreVM.Swaps

public section

namespace Silmaril.Machine.MulticoreVM

open Silmaril.Semantics.ConcurrentTrace (ofWord)

universe u

variable {State Thread Choice Event : Type u}
variable {step : Transition State Thread Choice Event} {initial : State}
variable {a b : Decision Thread Choice} {pre post source target : Schedule Thread Choice}
variable {allowed : Decision Thread Choice → Decision Thread Choice → Prop}

/-- To replay a pair, match every two-step outcome with a reversed execution to the same
final state. Compare the products of the named fragment classes in execution order. -/
theorem scheduleReplay_pair_iff :
    ScheduleReplay step initial [a, b] [b, a] ↔
      ∀ ⦃middle final first second⦄,
        step a.thread a.choice initial first middle →
        step b.thread b.choice middle second final →
        ∃ middle' first' second',
          step b.thread b.choice initial first' middle' ∧
          step a.thread a.choice middle' second' final ∧
          ofWord (nameFragment a.thread first) * ofWord (nameFragment b.thread second) =
            ofWord (nameFragment b.thread first') * ofWord (nameFragment a.thread second') :=
  Proofs.Machine.MulticoreVM.scheduleReplay_pair_iff

/-- A local diamond at every state reached by the prefix permits a swap in that context.
The replay keeps the prefix and suffix runs and uses the same state at each boundary. -/
theorem adjacent_swap_replay
    (diamond : ∀ ⦃middle word⦄, Scheduled step pre initial word middle →
      LocalDiamond step middle a b) :
    ScheduleReplay step initial (pre ++ a :: b :: post) (pre ++ b :: a :: post) ∧
      ScheduleReplay step initial (pre ++ b :: a :: post) (pre ++ a :: b :: post) :=
  Proofs.Machine.MulticoreVM.adjacent_swap_replay diamond

/-- An allowed pair can be exchanged inside any schedule context. -/
theorem ScheduleEquivalent.swap (h : allowed a b) :
    ScheduleEquivalent allowed (pre ++ a :: b :: post) (pre ++ b :: a :: post) :=
  Proofs.Machine.MulticoreVM.scheduleEquivalent_swap h

/-- The generated congruence replays successful runs in both directions, at each initial state. -/
theorem ScheduleEquivalent.replay (h : ScheduleEquivalent allowed source target)
    (sound : ∀ ⦃a b⦄, allowed a b → ∀ state, LocalDiamond step state a b)
    (initial : State) :
    ScheduleReplay step initial source target ∧ ScheduleReplay step initial target source :=
  Proofs.Machine.MulticoreVM.scheduleEquivalent_replay h sound initial

/-- Congruent schedules have equal sets of final-state and concurrent-trace observations. -/
theorem ScheduleEquivalent.quotient_outcomes_eq (h : ScheduleEquivalent allowed source target)
    (sound : ∀ ⦃a b⦄, allowed a b → ∀ state, LocalDiamond step state a b)
    (initial : State) :
    observeQuotient '' scheduledOutcomes step source initial =
      observeQuotient '' scheduledOutcomes step target initial :=
  Proofs.Machine.MulticoreVM.scheduleEquivalent_quotient_outcomes_eq h sound initial

end Silmaril.Machine.MulticoreVM
