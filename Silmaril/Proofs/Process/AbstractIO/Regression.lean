module

import Silmaril.Process.AbstractIO.Thms
import Silmaril.Process.AbstractIO.API.Defs
import Silmaril.Process.AbstractIO.Bridge.Defs
import Silmaril.Semantics.ITree.VisiblePrefix.Thms

namespace Silmaril.Process.AbstractIO.Regression

open Silmaril.Process.ITreeTrace
open Silmaril.Elgot.ITree

private def initial : Store where
  fds
    | 3 | 4 => some (.file 0)
    | 5 => some (.file 1)
    | 6 => some (.stream 0)
    | 7 => some (.stream 1)
    | _ => none
  descriptions
    | 0 | 1 => some ⟨0, 0, true, true⟩
    | _ => none
  files
    | 0 => some [10, 20, 30, 40]
    | _ => none
  streams
    | 0 => some { rx := [7, 8], peerFinished := true, sendRoom := 1 }
    | 1 => some {}
    | _ => none

private def threads : Pool signature Bool (IOResult Bytes)
  | false => call (.read 3 3) >>= fun _ => call (.read 3 3)
  | true => call (.read 4 2)

private theorem out_call_bind {A : Type} (req : Request) (next : Response req → Prog A) :
    out (call req >>= next) = Part.some (.vis (Event.call (sig := signature) req) next) :=
  (congrArg out (call_bind req next)).trans (out_vis _ _)

private def afterFirst := (step 0 initial (.read 3 3)).2
private def afterSecond := (step 3 afterFirst (.read 4 2)).2
private def afterThird := (step 3 afterSecond (.read 3 3)).2

-- The thread using fd 4 sees the advancement by fd 3. Both then share its advance.
example : Interleaving kernel [false, true, false] threads initial
    [(false, ⟨.read 3 3, .ok [10]⟩), (true, ⟨.read 4 2, .ok [20, 30]⟩),
      (false, ⟨.read 3 3, .ok [40]⟩)]
    (.returned fun tid => if tid then .ok [20, 30] else .ok [40]) afterThird := by
  refine Flatten.exchange (out_call_bind (.read 3 3) fun _ => call (.read 3 3))
    (step_completion 0 initial (.read 3 3)) ?_
  refine Flatten.exchange (out_vis _ _) (step_completion 3 afterFirst (.read 4 2)) ?_
  refine Flatten.exchange (out_vis _ _) (step_completion 3 afterSecond (.read 3 3)) ?_
  apply Flatten.returned
  intro tid
  cases tid with
  | false => exact out_ret (.ok [40] : IOResult Bytes)
  | true => exact out_ret (.ok [20, 30] : IOResult Bytes)

example : (afterThird.descriptions 0).map OpenFile.offset = some 4 := rfl
example : (afterThird.descriptions 1).map OpenFile.offset = some 0 := rfl
example : (step 3 afterThird (.read 5 2)).1 = .ok [10, 20] := rfl

private def afterWrite := (step 0 initial (.write 3 [1, 2, 3])).2
example : (step 0 initial (.write 3 [1, 2, 3])).1 = .ok 1 := rfl
example : afterWrite.files 0 = some [1, 20, 30, 40] := rfl
example : (step 1 afterWrite (.read 4 2)).1 = .ok [20, 30] := rfl
example : (step 0 initial (.pread 6 0 1)).1 = .error eIllegalSeek := rfl
example : (step 0 initial (.read 0 1)).1 = .error Syscall.Errno.badDescriptor := rfl

private def firstReceive := (step 0 initial (.recv 6 4)).2
private def secondReceive := (step 0 firstReceive (.recv 6 4)).2
example : (step 0 initial (.recv 6 4)).1 = .ok (.data [7]) := rfl
example : (step 0 firstReceive (.recv 6 4)).1 = .ok (.data [8]) := rfl
example : (step 0 secondReceive (.recv 6 4)).1 = .ok .eof := rfl
example : (step 0 secondReceive (.recv 6 0)).1 = .ok .zeroRequest := rfl
example : (step 0 initial (.recv 7 4)).1 = .ok .wouldBlock := rfl
example : (step 0 initial (.read 7 4)).1 = .error eAgain := rfl

private def copied := (step 0 (step 1 initial (.pread 3 1 3)).2 (.pwrite 5 5 [20, 30])).2

-- Interpret a high-level copy; the write accepts only one byte of the two read.
example : Sequential kernel 2 (fileAPI.map (trigger (Event.call (sig := fileSignature) (FileRequest.copyChunk ⟨3, 1⟩ ⟨5, 5⟩ 3)))) initial
    [⟨.pread 3 1 3, .ok [20, 30]⟩, ⟨.pwrite 5 5 [20, 30], .ok 1⟩]
    (.returned fun _ => .ok 1) copied := by
  rw [fileAPI.map_trigger]
  refine Flatten.exchange (out_call_bind (.pread 3 1 3) _)
    (step_completion 1 initial (.pread 3 1 3)) ?_
  refine Flatten.exchange (out_vis _ _)
    (step_completion 0 (step 1 initial (.pread 3 1 3)).2 (.pwrite 5 5 [20, 30])) ?_
  exact .returned (fun _ => out_ret _)

example : copied.files 0 = some [10, 20, 30, 40, 0, 20] := rfl
example : copied.descriptions = initial.descriptions := rfl

private def sent := (step 5 initial (.send 6 [1, 2, 3])).2

-- A send reports the unaccepted suffix and the buffer keeps only the accepted prefix.
example : Sequential kernel 1 (networkAPI.map (trigger (Event.call (sig := networkSignature) (NetworkRequest.sendChunk 6 [1, 2, 3])))) initial
    [⟨.send 6 [1, 2, 3], .ok (.count 1)⟩] (.returned fun _ => .ok (.remainder [2, 3])) sent := by
  rw [networkAPI.map_trigger]
  refine Flatten.exchange (out_call_bind (.send 6 [1, 2, 3]) _)
    (step_completion 5 initial (.send 6 [1, 2, 3])) ?_
  exact .returned (fun _ => out_ret _)

example : (sent.streams 0).map Stream.tx = some [1] := rfl
example : step 5 sent (.send 6 [2, 3]) = (.ok .wouldBlock, sent) := rfl

private def unavailable : TypedSyscall.Kernel signature Store Observation := fun _ _ _ _ => False

example : Sequential unavailable 1 (call (.read 3 1)) initial [] (.blocked () (.read 3 1)) initial :=
  .blocked (out_vis _ _) (by simp [unavailable])

example : Sequential kernel 0 (call (.read 3 1)) initial [] .exhausted initial := by
  apply Flatten.exhausted
  rintro ⟨values, done⟩
  have root := done ()
  change out (call (.read 3 1)) = _ at root
  have observed : out (call (.read 3 1)) =
      Part.some (.vis (Event.call (sig := signature) (.read 3 1)) ret) := out_vis _ _
  rw [observed] at root
  cases Part.some_inj.mp root

example : Sequential kernel 0 (ret 7) initial [] (.returned fun _ => 7) initial :=
  .returned (fun _ => out_ret _)

example : Sequential kernel 1 (diverge : Prog Unit) initial [] (.silent ()) initial :=
  .silent out_diverge

-- The generic runner also observes the existing typed Linux kernel's process exit.
private def abiInitial : Syscall.State := ⟨⟨[], {}⟩, fun _ => none, none⟩

private def abiExit : Program TypedSyscall.Linux.signature Unit :=
  vis (Event.call (sig := TypedSyscall.Linux.signature) (.exit 258)) (fun reply => nomatch reply)

example : Sequential TypedSyscall.Linux.kernel 1 abiExit abiInitial [.exit 2] (.exited 2)
    { abiInitial with exited := some 2 } :=
  .exited (out_vis _ _) (Syscall.Step.exit 258 rfl)

private theorem preadRun : Sequential kernel 1 (call (.pread 3 1 3)) initial
    [⟨.pread 3 1 3, .ok [20, 30]⟩] (.returned fun _ => .ok [20, 30]) initial :=
  .exchange (out_vis _ _) (step_completion 1 initial (.pread 3 1 3)) (.returned fun _ => out_ret _)

example : ∃ tagged, Interleaving kernel [()] (ITreeTrace.singleton (call (.pread 3 1 3))) initial
    tagged (.returned fun _ => .ok [20, 30]) initial ∧
    tagged.map Prod.snd = [⟨.pread 3 1 3, .ok [20, 30]⟩] :=
  sequential_iff_singleton.mp preadRun

example : Allows (call (.pread 3 1 3)) PositionedReads := pread_allows 3 1 3
example : VisibleDepthLE (call (.pread 3 1 3)) 1 :=
  visibleDepthLE_vis _ _ 0 (fun reply => visibleDepthLE_ret reply)

example : ofByteStreamRequest (fun _ _ => some [8]) (.write 3 1024 1) = some (.write 3 [8]) := rfl
example : ofByteStreamRequest (fun _ _ => some [8]) (.write 3 1024 2) = none := rfl
example : byteStreamResult (.read 3 4) (.ok [10, 20]) = some (.ok 2) := rfl
example : ofLpsFile 0 (.fileA [] 0) = none := rfl

end Silmaril.Process.AbstractIO.Regression
