module

public import Silmaril.Process.AbstractIO.Defs
public import Silmaril.Process.ITreeTrace.Thms
import Silmaril.Proofs.Process.AbstractIO.Transfer

public section

namespace Silmaril.Process.AbstractIO

open Silmaril.Elgot.ITree (vis)

theorem call_bind {A : Type} (req : Request) (next : Response req → Prog A) :
    (call req >>= next) = vis (ITreeTrace.Event.call (sig := signature) req) next :=
  Proofs.call_bind req next

/-- Every transfer choice gives a completed, typed observation. -/
theorem step_completion (choice : Nat) (before : Store) (req : Request) :
    kernel req before ⟨req, (step choice before req).1⟩
      (.returned (step choice before req).1 (step choice before req).2) :=
  ⟨choice, rfl, rfl⟩

/-- A positioned read preserves the entire shared store, including every
open file description, on success, EOF, and error. -/
theorem pread_store (choice : Nat) (store : Store) (fd offset count : Nat) :
    (step choice store (.pread fd offset count)).2 = store :=
  Proofs.pread_store choice store fd offset count

/-- A positioned write can change file bytes, leaving all descriptions intact. -/
theorem pwrite_descriptions (choice : Nat) (store : Store) (fd offset : Nat) (bytes : Bytes) :
    (step choice store (.pwrite fd offset bytes)).2.descriptions = store.descriptions :=
  Proofs.pwrite_descriptions choice store fd offset bytes

/-- A successful ordinary file read moves the shared offset by the bytes delivered. -/
theorem read_advances {store : Store} {fd id : Nat} {desc : OpenFile} {data delivered : Bytes}
    {choice count : Nat} (openFd : store.fds fd = some (.file id))
    (entry : fileEntry store fd none false = .ok (id, desc, data))
    (reply : (step choice store (.read fd count)).1 = .ok delivered) :
    (step choice store (.read fd count)).2.descriptions =
      Function.update store.descriptions id (some { desc with offset := desc.offset + delivered.length }) :=
  Proofs.read_advances openFd entry reply

/-- A successful ordinary file write moves the shared offset by the accepted count. -/
theorem write_advances {store : Store} {fd id : Nat} {desc : OpenFile} {data bytes : Bytes}
    {choice written : Nat} (openFd : store.fds fd = some (.file id))
    (entry : fileEntry store fd none true = .ok (id, desc, data))
    (reply : (step choice store (.write fd bytes)).1 = .ok written) :
    (step choice store (.write fd bytes)).2.descriptions =
      Function.update store.descriptions id (some { desc with offset := desc.offset + written }) :=
  Proofs.write_advances openFd entry reply

/-- Stream EOF needs a positive request, an empty receive queue and peer FIN. -/
theorem recv_eof {store : Store} {choice fd count : Nat}
    (reply : (step choice store (.recv fd count)).1 = .ok .eof) :
    ∃ id stream, streamEntry store fd = .ok (id, stream) ∧ stream.rx = [] ∧
      stream.peerFinished = true ∧ count ≠ 0 ∧ (step choice store (.recv fd count)).2 = store :=
  Proofs.recv_eof reply

/-- The tree satisfies the allowed-effect predicate on every finite path. -/
theorem pread_allows (fd offset count : Nat) :
    ITreeTrace.Allows (call (.pread fd offset count)) PositionedReads :=
  ITreeTrace.allows_vis (sig := signature) (req := .pread fd offset count)
    (permitted := PositionedReads) trivial (fun reply => ITreeTrace.allows_ret (sig := signature) reply _)

/-- Any finite run of positioned-read-only threads preserves the shared store,
including a run ending at a finite prefix. -/
theorem positioned_reads_store {Tid A Obs : Type} [DecidableEq Tid]
    {observe : Tid → Observation → Obs} {schedule : List Tid}
    {pool : ITreeTrace.Pool signature Tid A} {before after : Store}
    {trace : List Obs} {stop : ITreeTrace.End signature Tid A}
    (safe : ∀ tid, ITreeTrace.Allows (pool tid) PositionedReads)
    (run : ITreeTrace.Flatten kernel observe schedule pool before trace stop after) : after = before :=
  Proofs.positioned_reads_store safe run

end Silmaril.Process.AbstractIO
