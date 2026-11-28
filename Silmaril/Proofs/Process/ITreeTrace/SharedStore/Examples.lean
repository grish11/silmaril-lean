module

import Silmaril.Process.ITreeTrace.SharedStore.Thms
meta import Silmaril.Semantics.TrackA.Concurrency.Defs

namespace Silmaril.Process.ITreeTrace.SharedStore.Examples

open Silmaril.Elgot.ITree (out out_ret out_vis)
open Silmaril.Semantics.Brookes.TreeSC (Code Frame Request Store)
open Silmaril.Semantics.TrackA
open Concurrency (Config replay)

-- The first thread writes cell false. The second copies it into cell true.
private def threads : Bool → Code Bool
  | false => .store .scAtomic false 7 .done
  | true => .load .scAtomic false fun value => .store .scAtomic true value .done

private def initial : Store Bool := fun _ => 0
private def finish (copied : Nat) : Store Bool := fun cell => if cell then copied else 7

private def events (writerFirst : Bool) : List (Concurrency.Event Bool Empty Bool) :=
  let write : Concurrency.Event Bool Empty Bool := ⟨false, .write .scAtomic false 7⟩
  if writerFirst then [write, ⟨true, .read .scAtomic false 7⟩, ⟨true, .write .scAtomic true 7⟩]
  else [⟨true, .read .scAtomic false 0⟩, write, ⟨true, .write .scAtomic true 0⟩]

private def afterWrite : Store Bool := Function.update initial false 7
private def remaining : Bool → Code Bool := Function.update threads false .done

private theorem finish_eq (copied : Nat) : Function.update afterWrite true copied = finish copied := by
  funext cell
  cases cell <;> rfl

private theorem remaining_done (copied : Nat) :
    Function.update (Function.update remaining true (.store .scAtomic true copied .done)) true .done =
      (fun _ => .done) := by
  funext tid
  cases tid <;> rfl

private theorem writerFirst : Completes [false, true, true] threads initial (events true) (finish 7) := by
  apply completes_of_replay
  rw [← remaining_done 7, ← finish_eq]
  rfl

private theorem readerFirst : Completes [true, false, true] threads initial (events false) (finish 0) := by
  apply completes_of_replay
  have done : Function.update (Function.update (Function.update threads true
      (.store .scAtomic true 0 .done)) false .done) true .done = (fun _ => .done) := by
    funext tid
    cases tid <;> rfl
  rw [← done, ← finish_eq]
  rfl

example : ((threads false).denote.parallel (threads true).denote).completes initial (finish 7) ((), ()) :=
  parallel_completes_of_completes writerFirst

example : ((threads false).denote.parallel (threads true).denote).completes initial (finish 0) ((), ()) :=
  parallel_completes_of_completes readerFirst

-- The extra selection of the returned writer spends a slot but emits no event.
private theorem paddedRun : Completes [false, false, true, true] threads initial (events true) (finish 7) := by
  let req := Request.write .scAtomic false 7
  let frame : Frame Bool := ⟨⟨req, ()⟩, initial, afterWrite⟩
  have root : out (pool threads false) = Part.some
      (.vis (Event.call (sig := signature Bool) req) (fun _ => program .done)) := by
    change out (program (.store .scAtomic false 7 .done)) = _
    rw [program]
    exact out_vis _ _
  have step : kernel req initial frame (.returned () afterWrite) := ⟨rfl, rfl⟩
  have tail : Completes [true, true] remaining afterWrite (events true).tail (finish 7) :=
    by
      apply completes_of_replay
      rw [← remaining_done 7, ← finish_eq]
      rfl
  have skipped : Completes [false, true, true] remaining afterWrite (events true).tail (finish 7) := by
    refine .skip (out_ret ()) ?_ tail
    rintro ⟨values, returned⟩
    have readHead := returned true
    simp [pool, remaining, threads, program] at readHead
  have update : Function.update (pool threads) false (program .done) = pool remaining := by
    funext tid
    cases tid <;> rfl
  refine .exchange root step ?_
  rw [update]
  exact skipped

example : replay (Config.initial threads initial) [false, true, true] =
    some (events true, Config.initial (fun _ => .done) (finish 7)) :=
  (replay_of_completes paddedRun).2

private def readAndFinal (schedule : List Bool) : Option (Nat × Nat) := do
  let (events, last) ← replay (Config.initial threads initial) schedule
  let value ← events.findSome? fun e => match e.action with
    | .read _ _ value => some value
    | _ => none
  return (value, last.shared.memory true)

-- Run the existing SC replay. Each pair is (read reply, final value of cell true).
#guard readAndFinal [false, true, true] == some (7, 7)
#guard readAndFinal [true, false, true] == some (0, 0)

end Silmaril.Process.ITreeTrace.SharedStore.Examples
