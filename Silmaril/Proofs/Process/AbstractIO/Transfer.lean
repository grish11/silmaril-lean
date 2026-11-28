module

public import Silmaril.Process.AbstractIO.Defs
public import Silmaril.Process.ITreeTrace.Thms

public section

namespace Silmaril.Process.AbstractIO.Proofs

open ITreeTrace (Allows End Flatten Pool)
open Silmaril.Elgot.ITree (ret vis vis_bind)

theorem call_bind {A : Type} (req : Request) (next : Response req → Prog A) :
    (call req >>= next) = vis (ITreeTrace.Event.call (sig := signature) req) next := by
  let event := ITreeTrace.Event.call (sig := signature) req
  exact (vis_bind event ret next).trans
    (congrArg (vis event) (funext fun reply => pure_bind reply next))

theorem pread_store (choice : Nat) (store : Store) (fd offset count : Nat) :
    (step choice store (.pread fd offset count)).2 = store := by
  simp only [step, readFile]
  split <;> rfl

theorem pwrite_descriptions (choice : Nat) (store : Store) (fd offset : Nat) (bytes : Bytes) :
    (step choice store (.pwrite fd offset bytes)).2.descriptions = store.descriptions := by
  simp only [step, writeFile]
  split <;> rfl

theorem read_advances {store : Store} {fd id : Nat} {desc : OpenFile} {data delivered : Bytes}
    {choice count : Nat} (openFd : store.fds fd = some (.file id))
    (entry : fileEntry store fd none false = .ok (id, desc, data))
    (reply : (step choice store (.read fd count)).1 = .ok delivered) :
    (step choice store (.read fd count)).2.descriptions =
      Function.update store.descriptions id (some { desc with offset := desc.offset + delivered.length }) := by
  simp [step, openFd, readFile, entry, advance] at reply ⊢
  injection reply with transferred
  simp [← transferred]

theorem write_advances {store : Store} {fd id : Nat} {desc : OpenFile} {data bytes : Bytes}
    {choice written : Nat} (openFd : store.fds fd = some (.file id))
    (entry : fileEntry store fd none true = .ok (id, desc, data))
    (reply : (step choice store (.write fd bytes)).1 = .ok written) :
    (step choice store (.write fd bytes)).2.descriptions =
      Function.update store.descriptions id (some { desc with offset := desc.offset + written }) := by
  simp [step, openFd, writeFile, entry, advance] at reply ⊢
  injection reply with transferred
  simp [← transferred]

theorem recv_eof {store : Store} {choice fd count : Nat}
    (reply : (step choice store (.recv fd count)).1 = .ok .eof) :
    ∃ id stream, streamEntry store fd = .ok (id, stream) ∧ stream.rx = [] ∧
      stream.peerFinished = true ∧ count ≠ 0 ∧ (step choice store (.recv fd count)).2 = store := by
  cases entry : streamEntry store fd with
  | error error => simp [step, receive, entry] at reply
  | ok pair =>
      obtain ⟨id, stream⟩ := pair
      by_cases zero : count = 0
      · simp [step, receive, entry, zero] at reply
        injection reply with impossible
        cases impossible
      cases queue : stream.rx with
      | nil =>
          cases closed : stream.peerFinished with
          | false =>
              simp [step, receive, entry, zero, queue, closed] at reply
              injection reply with impossible
              cases impossible
          | true => exact ⟨id, stream, rfl, queue, closed, zero, by simp [step, receive, entry, zero, queue]⟩
      | cons head tail =>
          simp [step, receive, entry, zero, queue] at reply
          injection reply with impossible
          cases impossible

theorem positioned_reads_store {Tid A Obs : Type} [DecidableEq Tid]
    {observe : Tid → Observation → Obs} {schedule : List Tid} {pool : Pool signature Tid A}
    {before after : Store} {trace : List Obs} {stop : End signature Tid A}
    (safe : ∀ tid, Allows (pool tid) PositionedReads)
    (run : Flatten kernel observe schedule pool before trace stop after) : after = before := by
  induction run with
  | returned _ | exhausted _ | silent _ | blocked _ _ => rfl
  | exited _ completion =>
      obtain ⟨_, _, impossible⟩ := completion
      cases impossible
  | @exchange tid _ current store req next _ reply updated _ _ _ root completion _ ih =>
      obtain ⟨permitted, continuation⟩ := (safe tid).atCall root
      have unchanged : updated = store := by
        obtain ⟨choice, _, done⟩ := completion
        have same := congrArg (fun answer : TypedSyscall.Completion (Response req) Store =>
          match answer with | .returned _ state | .exited _ state => state) done
        cases req with
        | pread fd offset count => exact same.trans (pread_store choice store fd offset count)
        | _ => exact False.elim permitted
      refine (ih fun other => ?_).trans unchanged
      by_cases same : other = tid
      · subst other
        simpa only [Function.update_self] using continuation reply
      · simpa only [Function.update_of_ne same] using safe other
  | skip _ _ _ ih => exact ih safe

end Silmaril.Process.AbstractIO.Proofs
