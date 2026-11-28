module

import Silmaril.Machine.MulticoreVM.Synchronized.Physical.Thms

namespace Silmaril.Machine.MulticoreVM.Synchronized

open Scheduler (Advance Eligible Round Turn)
open Silmaril.Semantics.ConcurrentTrace (Word)

private abbrev Rig := Physical.Config (Fin 2)

private theorem twoSlots (core : Fin 2) : core = 0 ∨ core = 1 := by omega

private def occupy (left right : Option ThreadId) (core : Fin 2) : Option ThreadId :=
  if core = 0 then left else right

private def rig (vm : Config) (left right : Option ThreadId)
    (atLeft : left.all (fun t => (vm.threads t).isSome))
    (atRight : right.all (fun t => (vm.threads t).isSome))
    (distinct : left.isSome → left ≠ right) : Rig where
  cores := fun core => some (if core = 0 then vm.words else fun _ => 0)
  threads := vm.threads
  placement := occupy left right
  endpoints := by
    intro core thread atCore
    refine ⟨rfl, ?_⟩
    rcases twoSlots core with rfl | rfl
    · simpa only [show left = some thread from atCore, Option.all_some] using atLeft
    · simpa only [show right = some thread from atCore, Option.all_some] using atRight
  unique := by
    intro c d thread hc hd
    rcases twoSlots c with rfl | rfl <;> rcases twoSlots d with rfl | rfl
    · rfl
    · exact (distinct (by rw [show left = some thread from hc]; rfl) (hc.trans hd.symm)).elim
    · exact (distinct (by rw [show left = some thread from hd]; rfl) (hd.trans hc.symm)).elim
    · rfl

private def childCode : List Instr := [.wait 7 0, .emit]
private def parentTail : List Instr := [.yield, .store 7 11, .wake 7 1, .emit]

private def boot : Config :=
  ⟨fun _ => 0, fun t => if t = 0 then some (.runnable ⟨3, .spawn 9 childCode :: parentTail⟩) else none⟩
private def spawned := (boot.put 0 (.runnable ⟨3, parentTail⟩)).put 1 (.runnable ⟨9, childCode⟩)
private def waited := spawned.put 1 (.parked 7 ⟨0, [.emit]⟩)
private def yielded := waited.put 0 (.runnable ⟨3, [.store 7 11, .wake 7 1, .emit]⟩)
private def stored : Config :=
  { yielded.put 0 (.runnable ⟨3, [.wake 7 1, .emit]⟩) with words := fun k => if k = 7 then 11 else 0 }
private def woken := (stored.resume [1]).put 0 (.runnable ⟨1, [.emit]⟩)
private def final := woken.put 1 (.runnable ⟨0, []⟩)

private def start : Rig := rig boot (some 0) none rfl rfl (by decide)
private def childWaiting : Rig := rig spawned (some 0) none rfl rfl (by decide)
private def childPlaced : Rig := rig spawned (some 0) (some 1) rfl rfl (by decide)
private def childParked : Rig := rig waited (some 0) none rfl rfl (by decide)
private def bothIdle : Rig := rig yielded none none rfl rfl (by decide)
private def parentPlaced : Rig := rig yielded none (some 0) rfl rfl (by decide)
private def afterStore : Rig := rig stored none (some 0) rfl rfl (by decide)
private def afterWake : Rig := rig woken none (some 0) rfl rfl (by decide)
private def childRescheduled : Rig := rig woken (some 1) (some 0) rfl rfl (by decide)
private def finish : Rig := rig final none (some 0) rfl rfl (by decide)

private def corePolicy : Scheduler.CorePolicy (Fin 2) ThreadId Shared Slot := fun _ _ => True
private def threadPolicy : Scheduler.ThreadPolicy (Fin 2) ThreadId Shared Slot := fun _ _ _ => True

private theorem selectCore {cfg : Rig} {core : Fin 2} (present : (cfg.cores core).isSome) :
    corePolicy.Selects cfg core cfg :=
  ⟨trivial, present, rfl⟩

private theorem ready {cfg : Rig} {thread reg : Nat} {head : Instr} {rest : List Instr}
    (atThread : cfg.threads thread = some (.runnable ⟨reg, head :: rest⟩)) :
    Eligible Runnable cfg.threads thread :=
  ⟨_, atThread, List.cons_ne_nil _ _⟩

private theorem keep {cfg : Rig} {core : Fin 2} {thread : ThreadId}
    (atCore : cfg.placement core = some thread) (active : Eligible Runnable cfg.threads thread) :
    threadPolicy.Schedules Runnable core (.keep thread) cfg cfg :=
  ⟨trivial, (cfg.endpoints atCore).1, fun {_} h => Option.some.inj h ▸ active, .keep atCore⟩

private theorem assign {cfg next : Rig} {core : Fin 2} {thread : ThreadId}
    (present : (cfg.cores core).isSome) (unplaced : ∀ c, cfg.placement c ≠ some thread)
    (active : Eligible Runnable cfg.threads thread)
    (update : cfg.ReplacesPlacement next (Function.update cfg.placement core (some thread))) :
    threadPolicy.Schedules Runnable core (.assign thread) cfg next :=
  ⟨trivial, present, fun {_} h => Option.some.inj h ▸ active, .assign unplaced update⟩

private theorem writesOnlyMemory {cfg next : Rig} {words : Shared}
    (memory : next.cores 0 = some words) (other : next.cores 1 = cfg.cores 1) :
    next.cores = Function.update cfg.cores 0 (some words) := by
  funext core
  rcases twoSlots core with rfl | rfl
  · rwa [Function.update_self]
  · rwa [Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]

private theorem retain {cfg next : Rig} {core : Fin 2} {thread : ThreadId} {choice : Choice}
    {fragment : Fragment ThreadId Event} (atCore : cfg.placement core = some thread)
    (active : Eligible Runnable cfg.threads thread)
    (step : Physical.instruction 0 core thread choice cfg fragment next)
    (after : Eligible Runnable next.threads thread) (ordinary : fragment ≠ [.event .yield])
    (placement : next.placement = cfg.placement) :
    Advance Physical.lifecycle (Physical.instruction 0) core thread choice cfg
      (Placed.tagFragment core thread fragment) next :=
  .execute atCore ⟨active, step, fun release => (release.elim ordinary (fun h => h after)).elim,
    fun _ => placement⟩

private theorem release {cfg next : Rig} {core : Fin 2} {thread : ThreadId} {choice : Choice}
    {fragment : Fragment ThreadId Event} (atCore : cfg.placement core = some thread)
    (active : Eligible Runnable cfg.threads thread)
    (step : Physical.instruction 0 core thread choice cfg fragment next)
    (drops : Physical.lifecycle.ReleasesSlot thread choice cfg.threads fragment next.threads)
    (placement : next.placement = Function.update cfg.placement core none) :
    Advance Physical.lifecycle (Physical.instruction 0) core thread choice cfg
      (Placed.tagFragment core thread fragment) next :=
  .execute atCore ⟨active, step, fun _ => placement, fun h => (h drops).elim⟩

private theorem waitingChild : ∀ core, childWaiting.placement core ≠ some 1 := by
  intro core
  rcases twoSlots core with rfl | rfl <;> decide

private theorem spawnRound :
    Round corePolicy threadPolicy Physical.lifecycle (Physical.instruction 0)
      ⟨0, .keep 0, some (.spawn 1)⟩ start [.sync 0 0 [0, 1]] childWaiting := by
  refine .execute (selectCore rfl) (keep rfl (ready rfl)) rfl ?_
  exact retain (fragment := [.sync [0, 1]]) rfl (ready rfl)
    ⟨boot.words, spawned.words, rfl, rfl, writesOnlyMemory rfl rfl⟩ (ready rfl)
    (by intro h; cases h) rfl

private theorem placeRound :
    Round corePolicy threadPolicy Physical.lifecycle (Physical.instruction 0)
      ⟨1, .assign 1, none⟩ childWaiting [] childPlaced := by
  refine .place (selectCore rfl) (assign rfl waitingChild (ready rfl) ⟨rfl, rfl, ?_⟩)
  funext core
  rcases twoSlots core with rfl | rfl <;> rfl

private theorem parkedIneligible : ¬ Eligible Runnable childParked.threads 1 := by
  rintro ⟨slot, h, active⟩
  change some (.parked 7 ⟨0, [.emit]⟩) = some slot at h
  cases h
  exact active

private theorem waitRound :
    Round corePolicy threadPolicy Physical.lifecycle (Physical.instruction 0)
      ⟨1, .keep 1, some (.run [])⟩ childPlaced [.event 1 1 (.waitPark 7 0)] childParked := by
  refine .execute (selectCore rfl) (keep rfl (ready rfl)) rfl ?_
  refine release (fragment := [.event (.waitPark 7 0)]) rfl (ready rfl)
    ⟨spawned.words, waited.words, rfl, rfl, writesOnlyMemory rfl rfl⟩ (Or.inr parkedIneligible) ?_
  funext core
  rcases twoSlots core with rfl | rfl <;> rfl

private theorem yieldRound :
    Round corePolicy threadPolicy Physical.lifecycle (Physical.instruction 0)
      ⟨0, .keep 0, some (.run [])⟩ childParked [.event 0 0 .yield] bothIdle := by
  refine .execute (selectCore rfl) (keep rfl (ready rfl)) rfl ?_
  refine release (fragment := [.event .yield]) rfl (ready rfl)
    ⟨waited.words, yielded.words, rfl, rfl, writesOnlyMemory rfl rfl⟩ (Or.inl rfl) ?_
  funext core
  rcases twoSlots core with rfl | rfl <;> rfl

private theorem storeRound :
    Round corePolicy threadPolicy Physical.lifecycle (Physical.instruction 0)
      ⟨1, .assign 0, some (.run [])⟩ bothIdle [.event 1 0 (.store 7 11)] afterStore := by
  have placed := assign (cfg := bothIdle) (next := parentPlaced) (core := 1) (thread := 0)
    rfl (fun core => by rcases twoSlots core with rfl | rfl <;> decide) (ready rfl) ⟨rfl, rfl, by
      funext core
      rcases twoSlots core with rfl | rfl <;> rfl⟩
  refine .execute (selectCore rfl) placed rfl ?_
  exact retain (fragment := [.event (.store 7 11)]) rfl (ready rfl)
    ⟨yielded.words, stored.words, rfl, rfl, writesOnlyMemory rfl rfl⟩ (ready rfl)
    (by intro h; cases h) rfl

private theorem wakeAdvance :
    Advance Physical.lifecycle (Physical.instruction 0) 1 0 (.run [1]) afterStore
      [.event 1 0 (.wake 7 1 [1]), .sync 1 0 [0, 1]] afterWake :=
  retain (fragment := ThreadSync.wakeFragment 0 7 1 [1]) rfl (ready rfl)
    ⟨stored.words, woken.words, rfl, rfl, writesOnlyMemory rfl rfl⟩ (ready rfl)
    (by intro h; cases h) rfl

private theorem wakeRound :
    Round corePolicy threadPolicy Physical.lifecycle (Physical.instruction 0)
      ⟨1, .keep 0, some (.run [1])⟩ afterStore
      [.event 1 0 (.wake 7 1 [1]), .sync 1 0 [0, 1]] afterWake :=
  .execute (selectCore rfl) (keep rfl (ready rfl)) rfl wakeAdvance

private theorem wakeEligibility :
    Eligible Runnable afterWake.threads 1 ∧ ∀ core, afterWake.placement core ≠ some 1 :=
  wakeAdvance.eligible_waiter (fun core => by
    rcases twoSlots core with rfl | rfl <;> decide) (ready rfl)

private theorem doneIneligible : ¬ Eligible Runnable finish.threads 1 := by
  rintro ⟨slot, h, active⟩
  change some (.runnable ⟨0, []⟩) = some slot at h
  cases h
  exact active rfl

private theorem emitRound :
    Round corePolicy threadPolicy Physical.lifecycle (Physical.instruction 0)
      ⟨0, .assign 1, some (.run [])⟩ afterWake [.event 0 1 (.localOutput 0)] finish := by
  have placed := assign (cfg := afterWake) (next := childRescheduled) (core := 0) (thread := 1)
    rfl wakeEligibility.2 wakeEligibility.1 ⟨rfl, rfl, by
      funext core
      rcases twoSlots core with rfl | rfl <;> rfl⟩
  refine .execute (selectCore rfl) placed rfl ?_
  refine release (fragment := [.event (.localOutput 0)]) rfl (ready rfl)
    ⟨woken.words, final.words, rfl, rfl, writesOnlyMemory rfl rfl⟩ (Or.inr doneIneligible) ?_
  funext core
  rcases twoSlots core with rfl | rfl <;> rfl

private def schedule : List (Turn (Fin 2) ThreadId Choice) :=
  [⟨0, .keep 0, some (.spawn 1)⟩, ⟨1, .assign 1, none⟩, ⟨1, .keep 1, some (.run [])⟩,
   ⟨0, .keep 0, some (.run [])⟩, ⟨1, .assign 0, some (.run [])⟩, ⟨1, .keep 0, some (.run [1])⟩,
   ⟨0, .assign 1, some (.run [])⟩]

private def tagged : Placed.TaggedWord (Fin 2) ThreadId Event :=
  [.sync 0 0 [0, 1], .event 1 1 (.waitPark 7 0), .event 0 0 .yield, .event 1 0 (.store 7 11),
   .event 1 0 (.wake 7 1 [1]), .sync 1 0 [0, 1], .event 0 1 (.localOutput 0)]

private theorem twoCoreRun : Physical.Scheduled 0 corePolicy threadPolicy schedule start tagged finish :=
  .cons spawnRound (.cons placeRound (.cons waitRound (.cons yieldRound (.cons storeRound
    (.cons wakeRound (.cons emitRound (.nil _)))))))

private def observed : Word ThreadId Event :=
  [.sync [0, 1], .event 1 (.waitPark 7 0), .event 0 .yield, .event 0 (.store 7 11),
   .event 0 (.wake 7 1 [1]), .sync [0, 1], .event 1 (.localOutput 0)]

example : (final, observed) ∈ namedOutcomes (run step 6) boot :=
  Physical.Scheduled.mem_threadRun twoCoreRun

example : final.words 7 = 11 ∧ final.threads 1 = some (.runnable ⟨0, []⟩) :=
  ⟨rfl, rfl⟩

end Silmaril.Machine.MulticoreVM.Synchronized
