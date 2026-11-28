module

public import Silmaril.Machine.MulticoreVM.CriticalRegion.Defs
public import Silmaril.Machine.MulticoreVM.Cooperative.Thms

public section

namespace Silmaril.Proofs.Machine.MulticoreVM.CriticalRegion

open Silmaril.Machine.MulticoreVM Silmaril.Machine.MulticoreVM.CriticalRegion
open Silmaril.Semantics.ConcurrentTrace (Word)

universe u

variable {State Thread Instruction Event Abstract : Type u}
variable {program : Program State Thread Instruction Event}
variable {view : State → Abstract} {abstractStep : Transition Abstract Thread Instruction Event}
variable {step : Transition State Thread Instruction Event}

theorem scheduled_refines (refines : program.Refines view abstractStep)
    {moves : Schedule Thread (Action Instruction)} {initial final : Config State Thread}
    {word : Word Thread Event} (path : Scheduled (Step program) moves initial word final) :
    Scheduled abstractStep (atomicSchedule moves) (view initial.vm) word (view final.vm) := by
  induction path with
  | nil cfg => exact .nil (view cfg.vm)
  | @cons decision schedule initial next final fragment tail first _ ih =>
    cases decision with
    | mk thread action =>
      cases first with
      | atomic _ _ atomic => exact .cons (refines.atomic atomic) ih
      | enter _ enter => exact refines.enter_preserves enter ▸ ih
      | leave _ leave => exact refines.leave_preserves leave ▸ ih

theorem observedOutcomes_subset (refines : program.Refines view abstractStep)
    (initial : Config State Thread) (n : Nat) :
    observedOutcomes program view initial n ⊆ namedOutcomes (run abstractStep n) (view initial.vm) := by
  rintro ⟨final, word⟩ ⟨moves, target, len, path, same⟩
  change view target.vm = final at same
  subst final
  exact (mem_run_iff_exists_schedule n).2 ⟨atomicSchedule moves, len, scheduled_refines refines path⟩

theorem actor_eq_of_held {thread owner : Thread} {action : Action Instruction}
    {state : State} {next : Config State Thread} {fragment : Fragment Thread Event}
    (first : Step program thread action ⟨state, some owner⟩ fragment next) : thread = owner := by
  cases first with
  | atomic allowed _ _ => exact (Option.some.inj (allowed.resolve_left (by simp))).symm
  | leave => rfl

theorem held_without_leave {moves : Schedule Thread (Action Instruction)}
    {initial final : Config State Thread} {word : Word Thread Event} {owner : Thread}
    (path : Scheduled (Step program) moves initial word final) (held : initial.owner = some owner)
    (noLeave : ∀ decision ∈ moves, decision.choice ≠ .leave) :
    final.owner = some owner ∧ ∀ decision ∈ moves, decision.thread = owner := by
  induction path with
  | nil => exact ⟨held, by simp⟩
  | @cons decision schedule _ _ _ _ _ first _ ih =>
    have rest : ∀ d ∈ schedule, d.choice ≠ .leave :=
      fun d hd => noLeave d (List.mem_cons_of_mem _ hd)
    cases decision with
    | mk thread action =>
      cases first with
      | atomic allowed _ _ =>
        have same : thread = owner := by
          rcases allowed with free | own
          · rw [free] at held
            contradiction
          · rw [own] at held
            exact Option.some.inj held
        exact ⟨(ih held rest).1, by simpa using And.intro same (ih held rest).2⟩
      | enter => contradiction
      | leave => exact False.elim (noLeave _ (List.mem_cons_self ..) rfl)

theorem atomic_when_free {thread : Thread} {instruction : Instruction} {state next : State}
    {fragment : Fragment Thread Event} :
    Step program thread (.atomic instruction) (Config.start state) fragment (Config.start next) ↔
      ¬ program.finished thread state ∧ program.atomic thread instruction state fragment next := by
  constructor
  · intro first
    cases first with | atomic _ active step => exact ⟨active, step⟩
  · rintro ⟨active, step⟩
    exact .atomic (Or.inl rfl) active step

theorem atomicSchedule_liftSchedule (schedule : Schedule Thread Instruction) :
    atomicSchedule (liftSchedule schedule) = schedule := by
  induction schedule with
  | nil => rfl
  | cons decision schedule ih =>
    cases decision
    exact congrArg (List.cons _) ih

theorem scheduled_regionFree {schedule : Schedule Thread Instruction} {initial final : State}
    {word : Word Thread Event} (path : Scheduled step schedule initial word final) :
    Scheduled (Step (regionFree step)) (liftSchedule schedule)
      (Config.start initial) word (Config.start final) := by
  induction path with
  | nil => exact .nil _
  | cons first _ ih => exact .cons (.atomic (Or.inl rfl) id first) ih

theorem observedOutcomes_regionFree (step : Transition State Thread Instruction Event)
    (initial : State) (n : Nat) :
    observedOutcomes (regionFree step) id (Config.start initial) n =
      namedOutcomes (run step n) initial := by
  apply Set.Subset.antisymm
  · exact observedOutcomes_subset ⟨id, False.elim, False.elim⟩ _ _
  · rintro ⟨final, word⟩ run
    obtain ⟨schedule, len, path⟩ := (mem_run_iff_exists_schedule n).1 run
    exact ⟨liftSchedule schedule, Config.start final,
      (congrArg List.length (atomicSchedule_liftSchedule schedule)).trans len,
      scheduled_regionFree path, rfl⟩

end Silmaril.Proofs.Machine.MulticoreVM.CriticalRegion
