module

import Silmaril.Semantics.TrackA.Concurrency.Thms

/-! Checked examples over two threads. All closed computations use Lean's
kernel reduction. -/

namespace Silmaril.Semantics.TrackA.Concurrency.Examples

open Operational (explore)

private def twoThreads : List Bool := [false, true]

private theorem covers (t : Bool) : t ∈ twoThreads := by
  cases t <;> decide

private def generate {L R : Type} [DecidableEq L] [DecidableEq R] :=
  @enumerator Bool L R _ _ _ twoThreads covers

private def reached {L R : Type} [DecidableEq L] [DecidableEq R]
    (s : Config Bool L R) (schedule : List Bool) : Config Bool L R :=
  ((replay s schedule).getD ([], s)).2

private theorem run_of_replay {L R : Type} [DecidableEq L] [DecidableEq R]
    {s : Config Bool L R} {schedule : List Bool} {trace : List (Event Bool L R)}
    (h : replay s schedule = some (trace, reached s schedule)) :
    sc.MTr s trace (reached s schedule) :=
  (replay_iff.mp h).1

private def disjoint : SingleMutexConfig Bool Bool :=
  Config.initial (fun t => .store .plain t (if t then 2 else 1) .done) (fun _ => 0)

private def disjointView (out : List (Event Bool Unit Bool) × SingleMutexConfig Bool Bool) :
    Nat × Nat × RaceClass :=
  (out.2.shared.memory false, out.2.shared.memory true, classify .mutexOnly out.1)

/-- Both two-step schedules give the same two cells and are race-free. -/
theorem disjoint_resources :
    (explore (generate.next) 2 disjoint).map disjointView =
      [(1, 2, .clean), (1, 2, .clean)] := by
  decide

private def oppositeOrder : Config Bool Bool Unit :=
  Config.initial (fun t =>
    .acquire t (.acquire (!t) (.release (!t) (.release t .done)))) (fun _ => 0)

private def afterTwoLocks : Config Bool Bool Unit :=
  reached oppositeOrder [false, true]

/-- One thread holds each mutex and is pending on the other. Both have
unfinished work and the machine admits no successor. -/
theorem two_lock_deadlock :
    (∃ xs, GuardedRun .mutexOnly oppositeOrder xs afterTwoLocks) ∧
      afterTwoLocks.LockCycle₂ ∧ afterTwoLocks.Stuck := by
  refine ⟨⟨[⟨false, .acquire false⟩, ⟨true, .acquire true⟩], guarded_iff.mpr
      ⟨run_of_replay (schedule := [false, true]) rfl, by decide⟩⟩,
    ⟨false, true, false, true, by decide, rfl, rfl, ?_, ?_⟩, ?_⟩
  · exact ⟨⟨_, rfl⟩, by decide⟩
  · exact ⟨⟨_, rfl⟩, by decide⟩
  · refine ⟨?_, ?_⟩
    · intro e dest step
      change afterTwoLocks.stepFor e.thread = some (e, dest) at step
      have blocked : afterTwoLocks.stepFor e.thread = none := by
        cases e.thread <;> rfl
      simp [blocked] at step
    · intro done
      have pending : afterTwoLocks.code false = .acquire true _ := rfl
      rw [done false] at pending
      cases pending

/-- The same two-lock program can also complete, with empty ownership. -/
theorem two_lock_serial_completion :
    ((replay oppositeOrder [false, false, false, false, true, true, true, true]).map
      (fun out => (out.2.shared.owner false, out.2.shared.owner true))) = some (none, none) := by
  decide

private def publish : SingleMutexConfig Bool Bool :=
  Config.initial (fun
    | false => .store .plain false 7 (.store .scAtomic true 1 .done)
    | true => .load .scAtomic true fun _ => .load .plain false fun _ => .done) (fun _ => 0)

private def publishView (schedule : List Bool) :
    Option (List (Event Bool Unit Bool) × RaceClass × RaceClass) :=
  (replay publish schedule).map fun (trace, _) =>
    (trace, classify .mutexOnly trace, classify .mixed trace)

private def receivesPublication : List (Event Bool Unit Bool) :=
  [⟨false, .write .plain false 7⟩, ⟨false, .write .scAtomic true 1⟩,
   ⟨true, .read .scAtomic true 1⟩, ⟨true, .read .plain false 7⟩]

private def missesPublication : List (Event Bool Unit Bool) :=
  [⟨true, .read .scAtomic true 0⟩, ⟨false, .write .plain false 7⟩,
   ⟨false, .write .scAtomic true 1⟩, ⟨true, .read .plain false 7⟩]

/-- An actual atomic reads-from edge orders the plain payload accesses.
A consumer that reads the initial flag value races on the payload. -/
theorem mixed_publication :
    publishView [false, false, true, true] = some (receivesPublication, .racy, .clean) ∧
      publishView [true, false, false, true] = some (missesPublication, .racy, .racy) := by
  decide

private def forgedPublication : List (Event Bool Unit Bool) :=
  [⟨false, .write .plain false 7⟩, ⟨false, .write .scAtomic true 1⟩,
   ⟨true, .read .scAtomic true 0⟩, ⟨true, .read .plain false 7⟩]

/-- The raw tests use the label positions and accept the forged reads-from edge.
Replay rejects that history because the atomic read must return 1. -/
theorem forged_publication_rejected :
    atomicSync forgedPublication 1 2 (.write .scAtomic true 1) (.read .scAtomic true 0) = true ∧
      classify .mixed forgedPublication = .clean ∧
      classifyHistory .mixed publish forgedPublication = none ∧
      classifyHistory .mixed publish receivesPublication = some .clean ∧
      classifyHistory .mixed publish missesPublication = some .racy := by
  decide

/-- Filtering retains one complete schedule, while another schedule from
the same program reaches UB at its fourth operation. -/
theorem filter_can_hide_ub :
    (∃ finish, FilteredRun .mixed publish receivesPublication finish) ∧
      RaceUB .mixed publish missesPublication := by
  constructor
  · exact ⟨_, guarded_iff_filtered.mp (guarded_iff.mpr
      ⟨run_of_replay (schedule := [false, false, true, true]) rfl, by decide⟩)⟩
  · refine ⟨missesPublication.take 3, reached publish [true, false, false],
      ⟨true, .read .plain false 7⟩, reached publish [true, false, false, true], rfl, ?_, rfl, ?_⟩
    · exact guarded_iff.mpr ⟨run_of_replay (schedule := [true, false, false]) rfl, by decide⟩
    · decide

private def overwrite : SingleMutexConfig Bool Unit :=
  Config.initial (fun
    | false => .store .scAtomic () 1 (.store .plain () 1 .done)
    | true => .load .scAtomic () fun _ => .done) (fun _ => 0)

/-- Equal values do not revive synchronization after a plain overwrite.
The plain write and the later atomic read race with one another. -/
theorem plain_atomic_overwrite :
    ((replay overwrite [false, false, true]).map fun (trace, _) =>
      (happensBefore .mixed trace 0 2, racePair .mixed trace 1 2)) = some (false, true) := by
  decide

private def increment (mode : AccessMode) (next : Program Unit Unit) : Program Unit Unit :=
  .load mode () fun value => .store mode () (value + 1) next

private def atomicIncrements : SingleMutexConfig Bool Unit :=
  Config.initial (fun _ => increment .scAtomic .done) (fun _ => 0)

private def incrementView (s : SingleMutexConfig Bool Unit) (schedule : List Bool) :
    Option (Nat × RaceClass) :=
  (replay s schedule).map fun (trace, last) => (last.shared.memory (), classify .mixed trace)

/-- Each primitive access is SC atomic and the interleaving is race-free.
The lost update differs from both serial orders of the two whole calls. -/
theorem atomic_steps_can_lose_update :
    incrementView atomicIncrements [false, true, false, true] = some (1, .clean) ∧
      incrementView atomicIncrements [false, false, true, true] = some (2, .clean) ∧
      incrementView atomicIncrements [true, true, false, false] = some (2, .clean) := by
  decide

private def protectedIncrements : SingleMutexConfig Bool Unit :=
  Config.initial (fun _ => .acquire () (increment .plain (.release () .done))) (fun _ => 0)

/-- The two successful eight-step schedules give the serial final value
and release the mutex. Every access in the critical section is plain. -/
theorem protected_serial_result :
    (explore (generate.next) 8 protectedIncrements).map (fun (trace, last) =>
      (last.shared.memory (), last.shared.owner (), classify .mutexOnly trace)) =
      [(2, none, .clean), (2, none, .clean)] := by
  decide

private def agreesWhenDone (s : SingleMutexConfig Bool Unit) : Bool :=
  match s.code false, s.code true with
  | .done, .done => decide (s.shared.memory () = 2 ∧ s.shared.owner () = none)
  | _, _ => true

private theorem protected_checked {trace : List (Event Bool Unit Unit)}
    {finish : SingleMutexConfig Bool Unit} (run : sc.MTr protectedIncrements trace finish) :
    RaceFree .mutexOnly trace ∧ agreesWhenDone finish = true := by
  have noNinth : explore (generate.next) 9 protectedIncrements = [] := rfl
  have short : trace.length < 9 := by
    by_contra! longer
    have splitRun : sc.MTr protectedIncrements (trace.take 9 ++ trace.drop 9) finish := by
      simpa only [List.take_append_drop] using run
    obtain ⟨mid, firstNine, _⟩ := splitRun.split
    have member := (generate.mem_explore_iff 9 protectedIncrements _ mid).mpr
      ⟨List.length_take_of_le longer, firstNine⟩
    simp [noNinth] at member
  have checked : (List.range 9).all (fun n =>
      (explore (generate.next) n protectedIncrements).all
        (fun (events, last) => !(hasRace .mutexOnly events) && agreesWhenDone last)) = true := by
    decide
  have member := (generate.mem_explore_iff trace.length protectedIncrements trace finish).mpr
    ⟨rfl, run⟩
  have good := List.all_eq_true.mp (List.all_eq_true.mp checked _ (List.mem_range.mpr short)) _ member
  simpa using good

/-- Every reachable prefix of this mutex implementation is race-free. -/
theorem protected_race_safe : RaceSafe .mutexOnly protectedIncrements :=
  raceSafe_iff.mpr fun _ _ run => (protected_checked run).1

/-- Every completed execution of these two protected calls has the serial
final value and leaves the mutex free. -/
theorem protected_completed_matches_serial {trace : List (Event Bool Unit Unit)}
    {finish : SingleMutexConfig Bool Unit} (run : sc.MTr protectedIncrements trace finish)
    (done : finish.Done) : finish.shared.memory () = 2 ∧ finish.shared.owner () = none := by
  simpa [agreesWhenDone, done false, done true] using (protected_checked run).2

end Silmaril.Semantics.TrackA.Concurrency.Examples
