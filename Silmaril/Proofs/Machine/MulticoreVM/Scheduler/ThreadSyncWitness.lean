module

import Silmaril.Machine.MulticoreVM.Scheduler.Thms
import Silmaril.Machine.MulticoreVM.ThreadSync.Thms

namespace Silmaril.Machine.MulticoreVM.Scheduler

open Silmaril.Semantics.ConcurrentTrace (Word)

private inductive PC where
  | start | wait | resume | store | wake | report | done

private abbrev VM := ThreadSync.Config Nat Nat Nat PC
private abbrev Slot := ThreadSync.ThreadState Nat PC
private abbrev Event := ThreadSync.Event Nat Nat Nat Nat
private abbrev Rig := Config Unit Nat (Nat → Nat) Slot

private def program : ThreadSync.Program Nat Nat Nat PC Nat
  | _, .start => some (.yield .wait)
  | _, .wait => some (.wait 7 0 .done .resume)
  | _, .resume => some (.localStep .done none)
  | _, .store => some (.store 7 1 .wake)
  | _, .wake => some (.wake 7 1 (fun _ => .report))
  | _, .report => some (.localStep .done (some 1))
  | _, .done => none

private def life : Lifecycle Nat Slot (List Nat) Event where
  runnable thread
    | .runnable pc => (program thread pc).isSome
    | .parked .. => False
  releases _ _ _ fragment _ := fragment = [.event .yield]

private def view : Placed.StoreView Unit Nat (Nat → Nat) Slot VM :=
  fun cores threads => ⟨(cores ()).getD (fun _ => 0), threads⟩

private def instruction : Placed.Instruction Unit Nat (Nat → Nat) Slot (List Nat) Event :=
  fun _ thread choice initial fragment next =>
    ThreadSync.step program thread choice (view initial.cores initial.threads) fragment
      (view next.cores next.threads)

private theorem instruction_refines : instruction.RefinesBy view (ThreadSync.step program) :=
  fun {_ _ _ _ _ _} _ transition => transition

private def corePolicy : CorePolicy Unit Nat (Nat → Nat) Slot :=
  fun _ _ => True

private def threadPolicy : ThreadPolicy Unit Nat (Nat → Nat) Slot :=
  fun cfg core dispatch => match dispatch with
    | .idle => cfg.placement core = none
    | .keep _ | .assign _ => True
    | .migrate .. => False

private def rig (vm : VM) (resident : Option Nat)
    (allocated : ∀ ⦃thread⦄, resident = some thread → (vm.threads thread).isSome) : Rig where
  cores := fun _ => some vm.words
  threads := vm.threads
  placement := fun _ => resident
  endpoints := fun {_ _} atCore => ⟨rfl, allocated atCore⟩
  unique := fun {_ _ _} _ _ => Subsingleton.elim _ _

private def boot : VM :=
  ⟨fun _ => 0, fun
    | 0 => some (.runnable .start)
    | 1 => some (.runnable .store)
    | _ => none⟩

private def afterYield := boot.put 0 (.runnable .wait)
private def afterWait := afterYield.put 0 (.parked 7 .resume)
private def afterStore : VM :=
  { afterWait.put 1 (.runnable .wake) with words := fun k => if k = 7 then 1 else 0 }
private def afterWake := (afterStore.resume [0]).put 1 (.runnable .report)
private def afterResume := afterWake.put 0 (.runnable .done)

private def bootRig : Rig := rig boot (some 0) (by rintro _ ⟨⟩; rfl)
private def yielded : Rig := rig afterYield none (by intro _ h; cases h)
private def waiterAssigned : Rig := rig afterYield (some 0) (by rintro _ ⟨⟩; rfl)
private def parked : Rig := rig afterWait none (by intro _ h; cases h)
private def wakerAssigned : Rig := rig afterWait (some 1) (by rintro _ ⟨⟩; rfl)
private def stored : Rig := rig afterStore (some 1) (by rintro _ ⟨⟩; rfl)
private def woken : Rig := rig afterWake (some 1) (by rintro _ ⟨⟩; rfl)
private def waiterReassigned : Rig := rig afterWake (some 0) (by rintro _ ⟨⟩; rfl)
private def finished : Rig := rig afterResume none (by intro _ h; cases h)

private theorem selectCore {cfg : Rig} (present : (cfg.cores ()).isSome) :
    corePolicy.Selects cfg () cfg :=
  ⟨trivial, present, rfl⟩

private theorem keepThread {cfg : Rig} {thread : Nat}
    (atCore : cfg.placement () = some thread)
    (ready : Eligible life.runnable cfg.threads thread) :
    threadPolicy.Schedules life.runnable () (.keep thread) cfg cfg :=
  ⟨trivial, (cfg.endpoints atCore).1, fun {_} h => Option.some.inj h ▸ ready, .keep atCore⟩

private theorem assignThread {cfg next : Rig} {thread : Nat}
    (present : (cfg.cores ()).isSome) (waiting : cfg.placement () ≠ some thread)
    (ready : Eligible life.runnable cfg.threads thread)
    (cores : next.cores = cfg.cores) (threads : next.threads = cfg.threads)
    (assigned : next.placement () = some thread) :
    threadPolicy.Schedules life.runnable () (.assign thread) cfg next := by
  refine ⟨trivial, present, fun {_} h => Option.some.inj h ▸ ready,
    .assign (fun () => waiting) ⟨cores, threads, ?_⟩⟩
  funext c
  cases c
  rw [Function.update_self]
  exact assigned

private theorem advanceReleases {cfg next : Rig} {thread : Nat} {choice : List Nat}
    {fragment : Fragment Nat Event} (atCore : cfg.placement () = some thread)
    (ready : Eligible life.runnable cfg.threads thread)
    (step : instruction () thread choice cfg fragment next)
    (release : life.ReleasesSlot thread choice cfg.threads fragment next.threads)
    (cleared : next.placement () = none) :
    Advance life instruction () thread choice cfg (Placed.tagFragment () thread fragment) next := by
  refine .execute atCore ⟨ready, step, fun _ => ?_, fun stays => (stays release).elim⟩
  funext c
  cases c
  rw [Function.update_self]
  exact cleared

private theorem advanceRetains {cfg next : Rig} {thread : Nat} {choice : List Nat}
    {fragment : Fragment Nat Event} (atCore : cfg.placement () = some thread)
    (ready : Eligible life.runnable cfg.threads thread)
    (step : instruction () thread choice cfg fragment next)
    (retains : ¬ life.ReleasesSlot thread choice cfg.threads fragment next.threads)
    (same : next.placement = cfg.placement) :
    Advance life instruction () thread choice cfg (Placed.tagFragment () thread fragment) next :=
  .execute atCore ⟨ready, step, fun release => (retains release).elim, fun _ => same⟩

private theorem parkedIneligible : ¬ Eligible life.runnable parked.threads 0 := by
  rintro ⟨slot, allocated, ready⟩
  change some (.parked 7 .resume) = some slot at allocated
  cases allocated
  exact ready

example {next : Rig} : ¬ threadPolicy.Schedules life.runnable () (.assign 0) parked next :=
  fun dispatch => parkedIneligible (dispatch.2.2.1 rfl)

private theorem yieldAdvance :
    Advance life instruction () 0 [] bootRig [.event () 0 .yield] yielded :=
  advanceReleases (fragment := [.event .yield]) rfl ⟨_, rfl, rfl⟩ rfl (Or.inl rfl) rfl

private theorem waitAdvance :
    Advance life instruction () 0 [] waiterAssigned [.event () 0 (.waitPark 7 0)] parked :=
  advanceReleases (fragment := [.event (.waitPark 7 0)]) rfl ⟨_, rfl, rfl⟩ rfl
    (Or.inr parkedIneligible) rfl

private theorem storeAdvance :
    Advance life instruction () 1 [] wakerAssigned [.event () 1 (.store 7 1)] stored := by
  refine advanceRetains (fragment := [.event (.store 7 1)]) rfl ⟨_, rfl, rfl⟩ rfl ?_ rfl
  rintro (voluntary | blocked)
  · cases voluntary
  · exact blocked ⟨_, rfl, rfl⟩

private theorem wakeAdvance :
    Advance life instruction () 1 [0] stored [.event () 1 (.wake 7 1 [0]), .sync () 1 [1, 0]] woken := by
  refine advanceRetains (fragment := ThreadSync.wakeFragment 1 7 1 [0]) rfl ⟨_, rfl, rfl⟩ rfl ?_ rfl
  rintro (voluntary | blocked)
  · cases voluntary
  · exact blocked ⟨_, rfl, rfl⟩

private theorem resumeAdvance :
    Advance life instruction () 0 [] waiterReassigned [] finished := by
  refine advanceReleases (fragment := []) rfl ⟨_, rfl, rfl⟩ rfl (Or.inr ?_) rfl
  rintro ⟨slot, allocated, ready⟩
  change some (.runnable .done) = some slot at allocated
  cases allocated
  exact nomatch ready

-- The yield leaves an idle core with a runnable waiter. The core can get an opportunity
-- even when thread dispatch elects to leave it idle.
example : Round corePolicy threadPolicy life instruction ⟨(), .idle, none⟩ yielded [] yielded := by
  refine .place (selectCore rfl) ⟨rfl, rfl, ?_, .idle ⟨rfl, rfl, ?_⟩⟩
  · intro _ h
    cases h
  funext c
  cases c
  rw [Function.update_self]
  rfl

-- Wake restores eligibility but leaves the worker waiting for a slot, with the waker resident.
example : Eligible life.runnable woken.threads 0 ∧ (∀ c, woken.placement c ≠ some 0) ∧
    woken.placement () = some 1 := by
  have eligible := wakeAdvance.eligible_waiter (resident := 0) (fun () h => by cases h) ⟨_, rfl, rfl⟩
  exact ⟨eligible.1, eligible.2, rfl⟩

private def schedule : List (Turn Unit Nat (List Nat)) :=
  [⟨(), .keep 0, some []⟩, ⟨(), .assign 0, none⟩, ⟨(), .keep 0, some []⟩,
    ⟨(), .assign 1, some []⟩, ⟨(), .keep 1, some [0]⟩, ⟨(), .assign 0, some []⟩]

private def tagged : Placed.TaggedWord Unit Nat Event :=
  [.event () 0 .yield, .event () 0 (.waitPark 7 0), .event () 1 (.store 7 1),
    .event () 1 (.wake 7 1 [0]), .sync () 1 [1, 0]]

private theorem oneCoreRun : Scheduled corePolicy threadPolicy life instruction schedule bootRig tagged finished := by
  refine .cons (.execute (selectCore rfl) (keepThread (cfg := bootRig) (thread := 0)
    rfl ⟨_, rfl, rfl⟩) rfl yieldAdvance) ?_
  refine .cons (.place (selectCore rfl) (assignThread (cfg := yielded) (next := waiterAssigned)
    (thread := 0) rfl (by decide) ⟨_, rfl, rfl⟩ rfl rfl rfl)) ?_
  refine .cons (.execute (selectCore rfl) (keepThread (cfg := waiterAssigned) (thread := 0)
    rfl ⟨_, rfl, rfl⟩) rfl waitAdvance) ?_
  refine .cons (.execute (selectCore rfl)
    (assignThread (cfg := parked) (next := wakerAssigned) (thread := 1)
      rfl (by decide) ⟨_, rfl, rfl⟩ rfl rfl rfl) rfl storeAdvance) ?_
  refine .cons (.execute (selectCore rfl) (keepThread (cfg := stored) (thread := 1)
    rfl ⟨_, rfl, rfl⟩) rfl wakeAdvance) ?_
  exact .cons (.execute (selectCore rfl)
    (assignThread (cfg := woken) (next := waiterReassigned) (thread := 0)
      rfl (by decide) ⟨_, rfl, rfl⟩ rfl rfl rfl) rfl resumeAdvance) (.nil _)

private def named : Word Nat Event :=
  [.event 0 .yield, .event 0 (.waitPark 7 0), .event 1 (.store 7 1),
    .event 1 (.wake 7 1 [0]), .sync [1, 0]]

-- Only the placement-only turn disappears. The silent continuation still takes a step.
example : (afterResume, named) ∈ namedOutcomes (run (ThreadSync.step program) 5) boot :=
  oneCoreRun.mem_threadRun instruction_refines

example : afterResume.words 7 = 1 ∧ afterResume.threads 0 = some (.runnable .done) :=
  ⟨rfl, rfl⟩

end Silmaril.Machine.MulticoreVM.Scheduler
