module

public import Silmaril.Containers.SqliteVfs.Completed.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.CacheHit.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Defs
import Silmaril.Proofs.Containers.SqliteVfs.Completed.Decode

@[expose] public section

namespace Silmaril.Containers.SqliteVfs.Completed

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.MutationTrace

theorem completed_encode (trace : Trace) : completed (encode trace) = trace :=
  Proofs.Containers.SqliteVfs.Completed.completed_encode trace

/-- Every finite execution from idle has a valid trace recovered from its
sends. Only the pending case has a trailing receive, tracked in the ending
phase and outside the completed trace. -/
theorem completed_exec_iff {State : Type} {handler : Handler State} {start : State}
    {events : List Event} {finish : Phase State} :
    (machine handler).Exec Mach.seqPolicy (.idle start) events finish ↔
      ∃ current, Trace.Valid handler start (completed events) current ∧
        ((events = encode (completed events) ∧ finish = .idle current) ∨
          ∃ request, events = encode (completed events) ++ [.recv request] ∧
            finish = .pending current request) :=
  Proofs.Containers.SqliteVfs.Completed.completed_exec_iff

/-- A blocked observation is exactly the encoding of its recovered valid
completed exchanges. -/
theorem completed_blocked_iff {State : Type} {handler : Handler State} {start : State}
    {events : List Event} :
    (runtime handler).beh start (.blocked events) ↔
      events = encode (completed events) ∧ ∃ final, Trace.Valid handler start (completed events) final :=
  Proofs.Containers.SqliteVfs.Completed.completed_blocked_iff

/-- A blocked observation of retaining exchanges has a valid backing trace
whose final state agrees on the page and its observed handle mode. -/
theorem blocked_retaining_page (capacity : Nat) (start : FileState) (page : Page) (events : List Event)
    (observed : (runtime (readWrite capacity)).beh start (.blocked events))
    (allowed : ∀ exchange ∈ completed events, RetainsPage page exchange)
    (complete : page.offset + page.size ≤ start.bytes.length) (positive : 0 < page.size) :
    events = encode (completed events) ∧
      ∃ final, Trace.Valid (readWrite capacity) start (completed events) final ∧
        CacheHit.AgreesOnPage start final page ∧ final.mode page.handle = start.mode page.handle :=
  Proofs.Containers.SqliteVfs.Completed.blocked_retaining_page capacity start page events
    observed allowed complete positive

end Silmaril.Containers.SqliteVfs.Completed
