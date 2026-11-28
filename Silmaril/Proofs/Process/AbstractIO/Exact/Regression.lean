module

import Silmaril.Process.AbstractIO.Exact.Thms
import Silmaril.Process.AbstractIO.Thms
meta import Silmaril.Process.AbstractIO.Defs

namespace Silmaril.Process.AbstractIO.Exact.Tests

open Silmaril.Elgot.ITree
open Silmaril.Elgot.ITree.Exact (Config End Finish Observes Satisfies Sentence Step satisfies_lower)
open ITreeTrace (Event Sequential)
open ITreeTrace.Exact (lowering returned_iff_sequential)

private def initial : Store where
  fds
    | 3 => some (.file 0)
    | 4 => some (.file 1)
    | _ => none
  descriptions
    | 0 => some ⟨0, 0, true, false⟩
    | 1 => some ⟨1, 1, false, true⟩
    | _ => none
  files
    | 0 => some [10, 20]
    | 1 => some [30, 40]
    | _ => none

private def src : FilePosition := ⟨3, 1⟩
private def dst : FilePosition := ⟨4, 1⟩

private def post (before : Store) :
    Silmaril.Elgot.ITree.Exact.Observation profile (IOResult Nat) → Prop
  | .prefix _ => True
  | .finished _ (.returned result after) =>
    result = .ok 1 ∧ after.descriptions = before.descriptions ∧ after.files 1 = some [30, 20]
  | _ => False

private def sentence : Sentence profile positioned :=
  copySentence src dst 1 (· = initial) post

private abbrev State := Config profile target (IOResult Nat)

private noncomputable def start : State :=
  ((sentence.lower (lowering positionedCalls)).test, initial)

private def afterCopy : Store := (step 0 initial (.pwrite 4 1 [20])).2
private def afterRead : State := (call (.pwrite 4 1 [20]), initial)
private def afterWrite : State := (ret (.ok 1), afterCopy)
private def readLabel : Observation := ⟨.pread 3 1 1, .ok [20]⟩
private def writeLabel : Observation := ⟨.pwrite 4 1 [20], .ok 1⟩

private theorem cap_positive (choice : Nat) : 0 < transferCap choice := by
  simp [transferCap, Syscall.maxTransfer]

private theorem read_choice (choice : Nat) : step choice initial (.pread 3 1 1) = (.ok [20], initial) := by
  have cap := Nat.min_eq_left (cap_positive choice)
  change (Except.ok (([20] : Bytes).take (min 1 (transferCap choice))), initial) = _
  rw [cap]
  rfl

private theorem write_choice (choice : Nat) : step choice initial (.pwrite 4 1 [20]) = (.ok 1, afterCopy) := by
  have take : ([20] : Bytes).take (transferCap choice) = [20] :=
    List.take_of_length_le (cap_positive choice)
  simp only [step, writeFile]
  change (Except.ok (([20] : Bytes).take (transferCap choice)).length,
    { initial with
      files := Function.update initial.files 1
        (some (overwrite [30, 40] 1 (([20] : Bytes).take (transferCap choice)))) }) = _
  rw [take]
  rfl

private def copyNext : IOResult Bytes → Prog (IOResult Nat)
  | .error errno => ret (.error errno)
  | .ok [] => ret (.ok 0)
  | .ok bytes => call (.pwrite 4 1 bytes)

private theorem start_shape :
    start.1 = vis (Event.call (sig := signature) (.pread 3 1 1)) copyNext := by
  change (lowering positionedCalls).lower (positionedCopy src dst 1) = _
  rw [lower_positionedCopy, fileAPI.map_trigger]
  change copyChunk src dst 1 = _
  rw [copyChunk, call_bind]
  congr 1
  funext reply
  cases reply with
  | error => rfl
  | ok bytes => cases bytes <;> rfl

private theorem read_step (batch : List Observation) (t : State) :
    Step linuxKernel () start batch t ↔ batch = [readLabel] ∧ t = afterRead := by
  rcases t with ⟨tree, store⟩
  rw [show start = (start.1, initial) from rfl, start_shape]
  refine (call_step_iff (req := .pread 3 1 1)).trans ?_
  constructor
  · rintro ⟨choice, eq⟩
    rw [read_choice choice] at eq
    exact ⟨eq.1, Prod.ext eq.2.2 eq.2.1⟩
  · rintro ⟨rfl, eq⟩
    cases eq
    exact ⟨0, rfl, rfl, rfl⟩

private theorem write_step (batch : List Observation) (t : State) :
    Step linuxKernel () afterRead batch t ↔ batch = [writeLabel] ∧ t = afterWrite := by
  rcases t with ⟨tree, store⟩
  change Step linuxKernel () (vis (Event.call (sig := signature) (.pwrite 4 1 [20])) ret, initial) batch (tree, store) ↔ _
  refine (call_step_iff (req := .pwrite 4 1 [20])).trans ?_
  constructor
  · rintro ⟨choice, eq⟩
    rw [write_choice choice] at eq
    exact ⟨eq.1, Prod.ext eq.2.2 eq.2.1⟩
  · rintro ⟨rfl, eq⟩
    cases eq
    exact ⟨0, rfl, rfl, rfl⟩

private theorem finished_next {current next : State} {label : Observation} {log : List Observation}
    {last : End profile (IOResult Nat)}
    (advance : ∀ batch t, Step linuxKernel () current batch t ↔ batch = [label] ∧ t = next)
    (pending : ∀ a, current.1 ≠ ret a)
    (run : Observes linuxKernel () current (.finished log last)) :
    ∃ tail, log = label :: tail ∧ Observes linuxKernel () next (.finished tail last) := by
  obtain ⟨word, t, batch, path, done, eq⟩ := run
  cases path with
  | nil =>
    rcases current with ⟨tree, store⟩
    exact (pending _ (finish_iff.mp done).choose_spec.1).elim
  | cons first rest =>
    obtain ⟨rfl, rfl⟩ := (advance _ _).mp first
    exact ⟨_, eq, ⟨_, _, _, rest, done, rfl⟩⟩

private theorem finished_copy {log : List Observation} {last : End profile (IOResult Nat)}
    (run : Observes linuxKernel () start (.finished log last)) :
    log = [readLabel, writeLabel] ∧ last = .returned (.ok 1) afterCopy := by
  obtain ⟨_, rfl, afterPread⟩ := finished_next read_step
    (fun a => by rw [start_shape]; exact Ne.symm (ret_ne_vis a _ _)) run
  obtain ⟨_, rfl, afterPwrite⟩ := finished_next write_step
    (fun a => Ne.symm (ret_ne_vis a _ _)) afterPread
  obtain ⟨word, t, batch, path, done, eq⟩ := afterPwrite
  cases path with
  | nil =>
    change Finish linuxKernel () (ret (.ok 1), afterCopy) batch last at done
    obtain ⟨a, ha, rfl, rfl⟩ := finish_iff.mp done
    cases ret_inj.mp ha
    exact ⟨by simpa using eq, rfl⟩
  | cons first _ => simp [afterWrite, Step] at first

private theorem target_satisfies : Satisfies linuxKernel (sentence.lower (lowering positionedCalls)) := by
  rintro ⟨⟩ before (rfl : before = initial) obs run
  cases obs with
  | «prefix» => trivial
  | finished log last =>
    obtain ⟨_, rfl⟩ := finished_copy run
    exact ⟨rfl, rfl, rfl⟩
  | infinite log =>
    obtain ⟨batches, ⟨states, h0, advance⟩, _⟩ := run
    have h1 := ((read_step _ _).mp (h0 ▸ advance 0)).2
    have h2 := ((write_step _ _).mp (h1 ▸ advance 1)).2
    have impossible : Step linuxKernel () afterWrite (batches 2) (states 3) := h2 ▸ advance 2
    simp [afterWrite, Step] at impossible

-- The institution transports the verified contract of the actual lowered copy.
example : Satisfies (Silmaril.Elgot.ITree.Exact.Kernel.reduct (lowering positionedCalls) linuxKernel)
    sentence :=
  (satisfies_lower (lowering positionedCalls) linuxKernel sentence).mp target_satisfies

private def fileOperation : Prog (IOResult Nat) :=
  copyChunk src dst 1

-- The two-slot sequential run emits both concrete labels and uses the same final store.
private theorem copy_run : Sequential kernel 2 fileOperation initial [readLabel, writeLabel]
    (.returned fun _ => .ok 1) afterCopy := by
  rw [fileOperation, copyChunk, call_bind]
  exact .exchange (out_vis _ _) (step_completion 0 initial (.pread 3 1 1))
    (.exchange (out_vis _ _) (step_completion 0 initial (.pwrite 4 1 [20]))
      (.returned (fun _ => out_ret _)))

example : Observes linuxKernel () (fileOperation, initial)
    (.finished [readLabel, writeLabel] (.returned (.ok 1) afterCopy)) :=
  (returned_iff_sequential.mp copy_run).1

-- Substitute the real ordinary write. Both writes copy the same byte to the same
-- position, but the ordinary write incorrectly advances the destination descriptor.
private def wrongCalls : positionedSignature.Hom signature where
  request
    | .read p count => .pread p.fd p.offset count
    | .write p bytes => .write p.fd bytes
  response
    | .read .. | .write .. => id

private def wrongStore := (step 0 initial (.write 4 [20])).2
private def wrongLabel : Observation := ⟨.write 4 [20], .ok 1⟩

private theorem wrong_run : Sequential kernel 2 (sentence.lower (lowering wrongCalls)).test initial
    [readLabel, wrongLabel] (.returned fun _ => .ok 1) wrongStore := by
  change Sequential kernel 2 ((lowering wrongCalls).lower (positionedCopy src dst 1)) _ _ _ _
  rw [positionedCopy, Silmaril.Elgot.ITree.Exact.Signature.Hom.lower_vis]
  refine .exchange (out_vis _ _) (step_completion 0 initial (.pread 3 1 1)) ?_
  have tail : (lowering wrongCalls).lower (vis (Event.call (sig := positionedSignature) (.write dst [20])) ret) =
      call (.write 4 [20]) := by
    rw [Silmaril.Elgot.ITree.Exact.Signature.Hom.lower_vis]
    exact congrArg (vis _) (funext fun _ => Silmaril.Elgot.ITree.Exact.Signature.Hom.lower_ret _ _)
  change Sequential kernel 1 ((lowering wrongCalls).lower (vis (Event.call (sig := positionedSignature) (.write dst [20])) ret))
    initial [wrongLabel] (.returned fun _ => .ok 1) wrongStore
  rw [tail]
  exact .exchange (out_vis _ _) (step_completion 0 initial (.write 4 [20]))
    (.returned (fun _ => out_ret _))

private theorem wrong_target : ¬ Satisfies linuxKernel (sentence.lower (lowering wrongCalls)) := by
  intro holds
  have observed := (returned_iff_sequential.mp wrong_run).1
  have descriptions := (holds () initial rfl _ observed).2.1
  have offset := congrArg (fun table => (table 1).map OpenFile.offset) descriptions
  change some 2 = some 1 at offset
  contradiction

example : ¬ Satisfies (Silmaril.Elgot.ITree.Exact.Kernel.reduct (lowering wrongCalls) linuxKernel)
    sentence :=
  fun h => wrong_target ((satisfies_lower (lowering wrongCalls) linuxKernel sentence).mpr h)

private def noSendRoom : Store where
  fds := fun _ => some (.stream 0)
  streams := fun _ => some {}

private def sendAttempt := trigger (Event.call (sig := networkSignature) (.sendChunk 6 [20]))

-- Would-block completes the exchange with its own typed reply and the original store.
example : Observes linuxKernel () ((lowering networkCalls).lower sendAttempt, noSendRoom)
    (.finished [⟨.send 6 [20], .ok .wouldBlock⟩] (.returned (.ok .wouldBlock) noSendRoom)) := by
  rw [sendAttempt, lower_network_call, networkAPI.map_trigger]
  refine ((returned_iff_sequential (fuel := 1)).mp ?_).1
  change Sequential kernel 1 (sendChunk 6 [20]) _ _ _ _
  rw [sendChunk, call_bind]
  exact .exchange (out_vis _ _) (step_completion 0 noSendRoom (.send 6 [20]))
    (.returned (fun _ => out_ret _))

private def accepts (result : IOResult Nat) (after : Store) : Bool :=
  match result with
  | .error _ => false
  | .ok count => decide (count = 1 ∧ after.descriptions 1 = initial.descriptions 1 ∧
      after.files 1 = some [30, 20])

-- These guards evaluate the actual store transitions, including the rejected one.
#guard accepts (step 0 initial (.pwrite 4 1 [20])).1 afterCopy
#guard !accepts (step 0 initial (.write 4 [20])).1 wrongStore
#guard afterCopy.files 1 == wrongStore.files 1

end Silmaril.Process.AbstractIO.Exact.Tests
