module

public import Silmaril.Machine.MulticoreVM.ThreadSync.Thms

namespace Silmaril.Machine.MulticoreVM.ThreadSync

open Silmaril.Semantics.ConcurrentTrace (Word)

private inductive PC where
  | wait | mismatch | resumed | store | wake | report (count : Nat) | yield | done

private def program : Program Nat Nat Nat PC Nat
  | _, .wait => some (.wait 7 0 .mismatch .resumed)
  | _, .mismatch => some (.localStep .done (some 10))
  | _, .resumed => some (.localStep .done (some 20))
  | _, .store => some (.store 7 1 .wake)
  | _, .wake => some (.wake 7 1 .report)
  | _, .report count => some (.localStep .done (some count))
  | _, .yield => some (.yield .resumed)
  | _, .done => none

private def boot : Config Nat Nat Nat PC :=
  ⟨fun _ => 0, fun
    | 0 => some (.runnable .wait)
    | 1 => some (.runnable .store)
    | _ => none⟩

private def parked := boot.put 0 (.parked 7 .resumed)

private def stored : Config Nat Nat Nat PC :=
  { parked.put 1 (.runnable .wake) with words := fun key => if key = 7 then 1 else 0 }

private def finished := ((stored.resume [0]).put 1 (.runnable (.report 1))).put 0 (.runnable .done)

private def schedule : Schedule Nat (List Nat) := [⟨0, []⟩, ⟨1, []⟩, ⟨1, [0]⟩, ⟨0, []⟩]

private def observed : Word Nat (Event Nat Nat Nat Nat) :=
  [.event 0 (.waitPark 7 0), .event 1 (.store 7 1), .event 1 (.wake 7 1 [0]),
    .sync [1, 0], .event 0 (.localOutput 20)]

private theorem waitStoreWake : execute (exec program) schedule boot = some (finished, observed) := rfl

example : (finished, observed) ∈ namedOutcomes (run (step program) 4) boot :=
  (mem_run_iff_execute 4).mpr ⟨schedule, rfl, waitStoreWake⟩

example : finished.words 7 = 1 ∧ finished.words 8 = 0 ∧
    finished.threads 0 = some (.runnable .done) ∧
    finished.threads 1 = some (.runnable (.report 1)) :=
  ⟨rfl, rfl, rfl, rfl⟩

-- A store by itself leaves the waiter blocked.
example : exec program 0 [] parked = none := rfl
example : execute (exec program) [⟨0, []⟩, ⟨1, []⟩, ⟨0, []⟩] boot = none := rfl

-- A store before the comparison takes the runnable mismatch continuation.
example : (execute (exec program) [⟨1, []⟩, ⟨0, []⟩, ⟨0, []⟩] boot).map Prod.snd =
    some [.event 1 (.store 7 1), .event 0 (.waitMismatch 7 0 1),
      .event 0 (.localOutput 10)] := rfl

-- An empty early wake makes no deposit for the later wait.
private def earlyWake := boot.put 1 (.runnable .wake)

example : (execute (exec program) [⟨1, []⟩, ⟨0, []⟩] earlyWake).map Prod.snd =
    some [.event 1 (.wake 7 1 []), .event 0 (.waitPark 7 0)] := rfl

example : execute (exec program) [⟨1, []⟩, ⟨0, []⟩, ⟨0, []⟩] earlyWake = none := rfl

private def otherWaiters := (stored.put 2 (.parked 7 .resumed)).put 3 (.parked 8 .resumed)

-- Two same-key waiters give two valid choices at limit one. Only the selected one can step.
example : (execute (exec program) [⟨1, [2]⟩, ⟨2, []⟩] otherWaiters).map Prod.snd =
    some [.event 1 (.wake 7 1 [2]), .sync [1, 2], .event 2 (.localOutput 20)] := rfl

example : execute (exec program) [⟨1, [2]⟩, ⟨0, []⟩] otherWaiters = none := rfl
example : execute (exec program) [⟨1, [0]⟩, ⟨3, []⟩] otherWaiters = none := rfl
example : exec program 1 [0, 2] otherWaiters = none := rfl
example : exec program 1 [3] otherWaiters = none := rfl
example : exec program 1 [1] otherWaiters = none := rfl
example : exec program 1 [4] otherWaiters = none := rfl

private def wakeWith (limit : Nat) : Program Nat Nat Nat PC Nat :=
  fun _ _ => some (.wake 7 limit .report)

example : exec (wakeWith 2) 1 [0, 0] otherWaiters = none := rfl
example : exec (wakeWith 0) 1 [0] otherWaiters = none := rfl
example : (exec (wakeWith 0) 1 [] otherWaiters).map Prod.snd =
    some [.event (.wake 7 0 [])] := rfl

-- The cooperative dispatcher retains ownership across the store.
example : execute (cooperativeExec program) [⟨1, []⟩, ⟨0, []⟩] ⟨boot, none⟩ = none := rfl

private def beforeYield : DispatchState Nat Nat Nat PC :=
  ⟨boot.put 0 (.runnable .yield), some 0⟩

-- A yield is explicit, and the next choice can dispatch the same thread or another one.
example : (execute (cooperativeExec program) [⟨0, []⟩, ⟨0, []⟩] beforeYield).map Prod.snd =
    some [.event 0 .yield, .event 0 (.localOutput 20)] := rfl

example : (execute (cooperativeExec program) [⟨0, []⟩, ⟨1, []⟩] beforeYield).map Prod.snd =
    some [.event 0 .yield, .event 1 (.store 7 1)] := rfl

-- Park and exhaustion are also dispatch points.
example : (execute (cooperativeExec program)
    [⟨0, []⟩, ⟨1, []⟩, ⟨1, [0]⟩, ⟨1, []⟩, ⟨0, []⟩] ⟨boot, none⟩).map Prod.snd =
    some [.event 0 (.waitPark 7 0), .event 1 (.store 7 1), .event 1 (.wake 7 1 [0]),
      .sync [1, 0], .event 1 (.localOutput 1), .event 0 (.localOutput 20)] := rfl

end Silmaril.Machine.MulticoreVM.ThreadSync
