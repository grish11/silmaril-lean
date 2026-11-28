module

import Silmaril.Machine.MulticoreVM.Institution.Schedulers.Thms

namespace Silmaril.Proofs.Machine.MulticoreVM.Institution.Schedulers.Regression

open CategoryTheory
open Silmaril.Machine.MulticoreVM
open Silmaril.Machine.MulticoreVM.CriticalRegion
open Silmaril.Machine.MulticoreVM.Institution

private abbrev sourceSig : Sig := ⟨Bool, Unit, Nat⟩
private abbrev targetSig : Sig := ⟨Nat, Unit, Option Nat⟩

private def sigMap : sourceSig ⟶ targetSig where
  thread := ⟨fun b => if b then 1 else 0, by intro a b h; cases a <;> cases b <;> simp_all⟩
  core := id
  event := some

private inductive Op where
  | advance
  | publish

-- The state is a shared counter and the owner thread's continuation.
private def rawStep (thread : Bool) (op : Op) (state : Nat × Nat) (effect : Option Nat)
    (next : Nat × Nat) : Prop :=
  match thread, op with
  | false, .advance => state.2 = 1 ∧ effect = none ∧ next = (state.1 + 1, 2)
  | true, .publish => effect = some state.1 ∧ next = (state.1 + 10, state.2)
  | _, _ => False

private def observe : Option Nat → Fragment Bool Nat
  | none => []
  | some n => [.event n]

private def program : Program (Nat × Nat) sourceSig.ThreadId Op sourceSig.Event where
  atomic := interpretEffects (A := sourceSig) rawStep observe
  enter thread state next := thread = false ∧ state.2 = 0 ∧ next = (state.1, 1)
  leave thread state next := thread = false ∧ state.2 = 2 ∧ next = (state.1, 3)
  finished thread state := if thread then 10 ≤ state.1 else state.2 = 3

private def abstractStep : Transition Nat Bool Op Nat :=
  fun thread op state fragment next =>
    match thread, op with
    | false, .advance => fragment = [] ∧ next = state + 1
    | true, .publish => fragment = [.event state] ∧ next = state + 10
    | _, _ => False

private theorem refines : program.Refines Prod.fst abstractStep where
  atomic := by
    intro thread op state word next h
    change ∃ e, rawStep thread op state e next ∧ observe e = word at h
    obtain ⟨e, first, rfl⟩ := h
    cases thread <;> cases op <;> simp only [rawStep] at first
    · obtain ⟨_, rfl, rfl⟩ := first
      exact ⟨rfl, rfl⟩
    · obtain ⟨rfl, rfl⟩ := first
      exact ⟨rfl, rfl⟩
  enter_preserves := by
    rintro _ _ _ ⟨_, _, rfl⟩
    rfl
  leave_preserves := by
    rintro _ _ _ ⟨_, _, rfl⟩
    rfl

private def moves : Schedule Bool (Action Op) :=
  [⟨false, .enter⟩, ⟨false, .atomic .advance⟩, ⟨false, .leave⟩, ⟨true, .atomic .publish⟩]

private def effects : sourceSig.NamedWord := [.event true 1]

private theorem switched :
    Scheduled (Step program) moves (Config.start (0, 0)) effects (Config.start (11, 3)) := by
  refine .cons (next := ⟨(0, 1), some false⟩) (fragment := []) ?_ ?_
  · exact Step.enter (by simp [program]) ⟨rfl, rfl, rfl⟩
  refine .cons (next := ⟨(1, 2), some false⟩) (fragment := []) ?_ ?_
  · exact Step.atomic (Or.inr rfl) (by simp [program]) ⟨none, ⟨rfl, rfl, rfl⟩, rfl⟩
  refine .cons (next := Config.start (1, 3)) (fragment := []) ?_ ?_
  · exact Step.leave (by simp [program]) ⟨rfl, rfl, rfl⟩
  refine .cons (fragment := [.event 1]) ?_ (.nil _)
  exact Step.atomic (Or.inl rfl) (by simp [program]) ⟨some 1, ⟨rfl, rfl⟩, rfl⟩

example : program.Completed (Config.start (11, 3)) := by
  refine ⟨rfl, ?_⟩
  intro thread
  cases thread <;> simp [program, Config.start]

example : ¬ program.Completed ⟨(11, 3), some false⟩ := by
  intro h
  have same : (some false : Option Bool) = none := h.1
  cases same

-- The foreign instruction is enabled at this VM state, but excluded by the owner.
example : program.atomic true .publish (0, 1) [.event 0] (10, 1) :=
  ⟨some 0, ⟨rfl, rfl⟩, rfl⟩

example {next : Config (Nat × Nat) Bool} {fragment : Fragment Bool Nat} :
    ¬ Step program true (.atomic .publish) ⟨(0, 1), some false⟩ fragment next :=
  fun first => Bool.noConfusion (actor_eq_of_held first)

example {next : Config (Nat × Nat) Bool} :
    ¬ Step program false .enter ⟨(0, 1), some false⟩ [] next := by
  intro first
  cases first

example {next : Config (Nat × Nat) Bool} :
    ¬ Step program false .leave (Config.start (1, 2)) [] next := by
  intro first
  cases first

-- Enter and leave advance the private continuation, and the silent atomic instruction
-- still contributes one unit to the erased count.
example : (11, effects) ∈ namedOutcomes (run abstractStep 2) 0 :=
  (mem_run_iff_exists_schedule 2).2 ⟨atomicSchedule moves, rfl, scheduled_refines refines switched⟩

example : (2, effects) ∈ (Scheduler.critical (regionFree abstractStep)).countedModel (Config.start 0) := by
  rw [Scheduler.countedModel_regionFree (A := sourceSig), Scheduler.mem_atomic_counted]
  exact ⟨11, (mem_run_iff_exists_schedule 2).2
    ⟨atomicSchedule moves, rfl, scheduled_refines refines switched⟩⟩

example : (2, effects) ∈
    (Scheduler.cooperative (Cooperative.everyAtomic abstractStep) Cooperative.anyDispatch).countedModel
      (Cooperative.Config.start (0, false)) := by
  rw [Scheduler.countedModel_everyAtomic (A := sourceSig), Scheduler.mem_atomic_counted]
  exact ⟨11, (mem_run_iff_exists_schedule 2).2
    ⟨atomicSchedule moves, rfl, scheduled_refines refines switched⟩⟩

-- The second interpretation changes names, state, instruction and effect carriers.
-- Its effect language is a list of reports and its extra state records a mode.
private def encodeState (s : Nat × Nat) : Bool × (Nat × Nat) := (false, s)
private def encodeEffect (e : Option Nat) : List Nat := e.toList

private def targetRaw (thread : Nat) (op : Option Op) (state : Bool × (Nat × Nat))
    (effect : List Nat) (next : Bool × (Nat × Nat)) : Prop :=
  match thread, op with
  | 0, some .advance => state.2.2 = 1 ∧ effect = [] ∧ next = (state.1, state.2.1 + 1, 2)
  | 1, some .publish => effect = [state.2.1] ∧ next = (state.1, state.2.1 + 10, state.2.2)
  | _, _ => False

private def targetObserve (report : List Nat) : Fragment Nat (Option Nat) :=
  report.map fun n => .event (some n)

private def targetProgram : Program (Bool × (Nat × Nat)) targetSig.ThreadId (Option Op) targetSig.Event where
  atomic := interpretEffects (A := targetSig) targetRaw targetObserve
  enter thread state next := thread = 0 ∧ state.2.2 = 0 ∧ next = (state.1, state.2.1, 1)
  leave thread state next := thread = 0 ∧ state.2.2 = 2 ∧ next = (state.1, state.2.1, 3)
  finished thread state := if thread = 1 then 10 ≤ state.2.1 else state.2.2 = 3

private def programMap : CriticalMap sigMap program targetProgram where
  toStepMap := StepMap.ofEffects sigMap encodeState some encodeEffect (by
    intro thread op state e next h
    cases thread <;> cases op <;> simp only [rawStep] at h
    · obtain ⟨ready, rfl, rfl⟩ := h
      exact ⟨ready, rfl, rfl⟩
    · obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩) (by intro e; cases e <;> rfl)
  finished := by
    intro thread state
    cases thread <;> exact id
  enter := by
    rintro _ _ _ ⟨rfl, ready, rfl⟩
    exact ⟨rfl, ready, rfl⟩
  leave := by
    rintro _ _ _ ⟨rfl, ready, rfl⟩
    exact ⟨rfl, ready, rfl⟩

private def sourceWord : sourceSig.ScheduledWord :=
  ([(false, .enter), (false, .atomic), (false, .leave), (true, .atomic)], effects)

private theorem sourceMember :
    sourceWord ∈ (Scheduler.critical program).model (Config.start (0, 0)) :=
  ⟨moves, effects, Config.start (11, 3), switched, rfl⟩

example : (2, [.event 1 (some 1)]) ∈
    (Scheduler.critical targetProgram).countedModel (Config.start (false, 0, 0)) :=
  programMap.schedulerForward.countedModel_image_subset (Config.start (0, 0))
    ⟨(2, effects), ⟨sourceWord, sourceMember, rfl⟩, rfl⟩

example : (Sentence.possible sourceWord).Holds
    (reduct sigMap.mapScheduled ((Scheduler.critical targetProgram).model
      (Config.start (false, 0, 0)))) :=
  (Scheduler.satisfaction_renaming sigMap (Scheduler.critical targetProgram) _
    (.possible sourceWord)).1
    (programMap.schedulerForward.model_image_subset (Config.start (0, 0)) ⟨sourceWord, sourceMember, rfl⟩)

end Silmaril.Proofs.Machine.MulticoreVM.Institution.Schedulers.Regression
