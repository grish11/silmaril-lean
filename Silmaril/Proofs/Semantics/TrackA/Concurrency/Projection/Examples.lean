module

import Silmaril.Semantics.TrackA.Concurrency.Projection.Thms
import Silmaril.Semantics.TrackA.Concurrency.Thms

/-! Counterexamples from concrete SC schedules. The trace computations use
kernel reduction. -/

namespace Silmaril.Semantics.TrackA.Concurrency.Projection.Examples

private def handoff : SingleMutexConfig Bool Unit :=
  Config.initial (fun t =>
    .acquire () (.store .plain () (if t then 2 else 1) (.release () .done))) (fun _ => 0)

private def handoffTrace : List (Event Bool Unit Unit) :=
  [⟨false, .acquire ()⟩, ⟨false, .write .plain () 1⟩, ⟨false, .release ()⟩,
   ⟨true, .acquire ()⟩, ⟨true, .write .plain () 2⟩, ⟨true, .release ()⟩]

private def hideLocks : Interface Unit Unit := ⟨fun _ => false, fun _ => true⟩

/-- Deleting the mutex handoff makes the two retained writes appear to race. -/
theorem hiding_lock_handoff :
    (∃ finish, sc.MTr handoff handoffTrace finish) ∧
      racePair .mutexOnly handoffTrace 1 4 = false ∧
      racePair .mutexOnly (hideLocks.observe handoffTrace) 0 1 = true ∧
      classify .mutexOnly handoffTrace = .clean ∧
      classify .mutexOnly (hideLocks.observe handoffTrace) = .racy := by
  refine ⟨⟨_, (replay_iff.mp (show
    replay handoff [false, false, false, true, true, true] = some (handoffTrace, _) from rfl)).1⟩,
    by decide⟩

private inductive Publisher where
  | producer
  | overwriter
  | consumer
  deriving DecidableEq

private def publish : SingleMutexConfig Publisher Bool :=
  Config.initial (fun
    | .producer => .store .plain false 7 (.store .scAtomic true 1 .done)
    | .overwriter => .store .scAtomic true 1 .done
    | .consumer => .load .scAtomic true fun _ => .load .plain false fun _ => .done) (fun _ => 0)

private def publishTrace : List (Event Publisher Unit Bool) :=
  [⟨.producer, .write .plain false 7⟩, ⟨.producer, .write .scAtomic true 1⟩,
   ⟨.overwriter, .write .scAtomic true 1⟩,
   ⟨.consumer, .read .scAtomic true 1⟩, ⟨.consumer, .read .plain false 7⟩]

private def withoutOverwrite : List (Event Publisher Unit Bool) :=
  publishTrace.take 2 ++ publishTrace.drop 3

private def deleteOverwrite : Projection publishTrace withoutOverwrite where
  index i := ⟨if i.val < 2 then i.val else i.val + 1, by
    have bound : i.val < 4 := i.isLt
    change _ < 5
    split <;> omega⟩
  mono := by
    intro i j ordered
    change i.val < j.val at ordered
    change (if i.val < 2 then i.val else i.val + 1) < (if j.val < 2 then j.val else j.val + 1)
    split <;> split <;> omega
  event_eq := by
    rintro ⟨i, bound⟩
    change i < 4 at bound
    have values : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases values with rfl | rfl | rfl | rfl <;> rfl

/-- The load reads the third thread's write, even though both flag writes
have the same value. Removing the actual writer fabricates an edge from
the producer and suppresses a race on the retained payload accesses. -/
theorem hiding_overwrite :
    (∃ finish, sc.MTr publish publishTrace finish) ∧
      ¬ deleteOverwrite.CoversOverwrites ∧
      direct .mixed publishTrace 2 3 = true ∧
      direct .mixed publishTrace 1 3 = false ∧
      direct .mixed withoutOverwrite 1 2 = true ∧
      racePair .mixed publishTrace 0 4 = true ∧
      racePair .mixed withoutOverwrite 0 3 = false := by
  refine ⟨⟨_, (replay_iff.mp (show
    replay publish [.producer, .producer, .overwriter, .consumer, .consumer] =
      some (publishTrace, _) from rfl)).1⟩, ?_, by decide⟩
  intro covers
  let write : Fin withoutOverwrite.length := ⟨1, by decide⟩
  let read : Fin withoutOverwrite.length := ⟨2, by decide⟩
  have overwritten : HasOverwrite publishTrace (deleteOverwrite.index write)
      (deleteOverwrite.index read) true := ⟨⟨2, by decide⟩, by decide, by decide, rfl⟩
  obtain ⟨k, after, before, _⟩ := covers write read true 1 1 rfl rfl overwritten
  change 1 < k.val at after
  change k.val < 2 at before
  omega

private def flagOnly : Interface Unit Bool := ⟨fun _ => true, id⟩

/-- Keeping all synchronizing resources can still hide every racing pair
when the conflicting accesses are to a private plain resource. -/
theorem hiding_conflict :
    flagOnly.CoversSynchronization .mixed publishTrace ∧
      classify .mixed publishTrace = .racy ∧
      classify .mixed (flagOnly.observe publishTrace) = .clean := by
  refine ⟨⟨?_, ?_⟩, by decide⟩
  · intro k lock isMutex
    rfl
  · rintro _ ⟨k, bound⟩ loc value atomic
    cases loc with
    | true => rfl
    | false =>
      change k < 5 at bound
      have values : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
      rcases values with rfl | rfl | rfl | rfl | rfl <;> simp [publishTrace] at atomic

/-- Identical visible labels still map to distinct source occurrences. -/
theorem repeated_labels :
    let e : Event Bool Unit Bool := ⟨false, .write .plain true 1⟩
    let trace := [e, ⟨true, .write .plain false 2⟩, e]
    (List.finRange (flagOnly.observe trace).length).map (fun i =>
      ((flagOnly.projection trace).index i).val) = [0, 2] := by
  decide

end Silmaril.Semantics.TrackA.Concurrency.Projection.Examples
