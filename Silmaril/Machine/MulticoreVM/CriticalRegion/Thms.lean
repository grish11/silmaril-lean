module

public import Silmaril.Machine.MulticoreVM.CriticalRegion.Defs
public import Silmaril.Machine.MulticoreVM.Cooperative.Thms
import Silmaril.Proofs.Machine.MulticoreVM.CriticalRegion.Comparison

public section

namespace Silmaril.Machine.MulticoreVM.CriticalRegion

open Silmaril.Semantics.ConcurrentTrace (Word)

universe u

variable {State Thread Instruction Event Abstract : Type u}
variable {program : Program State Thread Instruction Event}
variable {view : State → Abstract} {abstractStep : Transition Abstract Thread Instruction Event}
variable {step : Transition State Thread Instruction Event}

/-- Erasure gives an atomic schedule with the same chronological effects and the
projected endpoints. Its length counts all ordinary instructions, including silent ones. -/
theorem scheduled_refines (refines : program.Refines view abstractStep)
    {moves : Schedule Thread (Action Instruction)} {initial final : Config State Thread}
    {word : Word Thread Event} (path : Scheduled (Step program) moves initial word final) :
    Scheduled abstractStep (atomicSchedule moves) (view initial.vm) word (view final.vm) :=
  Proofs.Machine.MulticoreVM.CriticalRegion.scheduled_refines refines path

theorem observedOutcomes_subset (refines : program.Refines view abstractStep)
    (initial : Config State Thread) (n : Nat) :
    observedOutcomes program view initial n ⊆ namedOutcomes (run abstractStep n) (view initial.vm) :=
  Proofs.Machine.MulticoreVM.CriticalRegion.observedOutcomes_subset refines initial n

theorem actor_eq_of_held {thread owner : Thread} {action : Action Instruction}
    {state : State} {next : Config State Thread} {fragment : Fragment Thread Event}
    (first : Step program thread action ⟨state, some owner⟩ fragment next) : thread = owner :=
  Proofs.Machine.MulticoreVM.CriticalRegion.actor_eq_of_held first

/-- A segment wholly inside a region has only the owner's decisions and retains ownership.
The closing leave itself is also subject to `actor_eq_of_held`. -/
theorem held_without_leave {moves : Schedule Thread (Action Instruction)}
    {initial final : Config State Thread} {word : Word Thread Event} {owner : Thread}
    (path : Scheduled (Step program) moves initial word final) (held : initial.owner = some owner)
    (noLeave : ∀ decision ∈ moves, decision.choice ≠ .leave) :
    final.owner = some owner ∧ ∀ decision ∈ moves, decision.thread = owner :=
  Proofs.Machine.MulticoreVM.CriticalRegion.held_without_leave path held noLeave

/-- After a leave, every enabled ordinary transition is available, including the
former owner's and any other thread's. -/
theorem atomic_when_free {thread : Thread} {instruction : Instruction} {state next : State}
    {fragment : Fragment Thread Event} :
    Step program thread (.atomic instruction) (Config.start state) fragment (Config.start next) ↔
      ¬ program.finished thread state ∧ program.atomic thread instruction state fragment next :=
  Proofs.Machine.MulticoreVM.CriticalRegion.atomic_when_free

theorem atomicSchedule_liftSchedule (schedule : Schedule Thread Instruction) :
    atomicSchedule (liftSchedule schedule) = schedule :=
  Proofs.Machine.MulticoreVM.CriticalRegion.atomicSchedule_liftSchedule schedule

theorem scheduled_regionFree {schedule : Schedule Thread Instruction} {initial final : State}
    {word : Word Thread Event} (path : Scheduled step schedule initial word final) :
    Scheduled (Step (regionFree step)) (liftSchedule schedule)
      (Config.start initial) word (Config.start final) :=
  Proofs.Machine.MulticoreVM.CriticalRegion.scheduled_regionFree path

theorem observedOutcomes_regionFree (step : Transition State Thread Instruction Event)
    (initial : State) (n : Nat) :
    observedOutcomes (regionFree step) id (Config.start initial) n =
      namedOutcomes (run step n) initial :=
  Proofs.Machine.MulticoreVM.CriticalRegion.observedOutcomes_regionFree step initial n

/-- Exact comparison through the common atomic observation, with the yield-only
dispatcher explicitly instrumented to yield after each ordinary instruction. -/
theorem observedOutcomes_everyAtomic (step : Transition State Thread Instruction Event)
    (initial : State) (n : Nat) :
    observedOutcomes (regionFree step) id (Config.start initial) n =
      Cooperative.observedOutcomes (Cooperative.everyAtomic step) Cooperative.anyDispatch Prod.fst
        (Cooperative.Config.start (initial, false)) n :=
  (observedOutcomes_regionFree step initial n).trans
    (Cooperative.observedOutcomes_everyAtomic step initial n).symm

end Silmaril.Machine.MulticoreVM.CriticalRegion
