module

public import Silmaril.Containers.SqliteVfs.Completed.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.CacheHit.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Defs
import Silmaril.Containers.SqliteVfs.Thms
import Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Thms

public section

namespace Silmaril.Proofs.Containers.SqliteVfs.Completed

open Silmaril.Containers
open Silmaril.Containers.SqliteVfs
open Silmaril.Containers.SqliteVfs.Completed
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.MutationTrace

theorem completed_encode (trace : Trace) : completed (encode trace) = trace := by
  induction trace with
  | nil => rfl
  | cons exchange rest ih =>
    change exchange :: completed (encode rest) = exchange :: rest
    rw [ih]

theorem completed_exec_iff {State : Type} {handler : Handler State} {start : State}
    {events : List Event} {finish : Phase State} :
    (machine handler).Exec Mach.seqPolicy (.idle start) events finish ↔
      ∃ current, Trace.Valid handler start (completed events) current ∧
        ((events = encode (completed events) ∧ finish = .idle current) ∨
          ∃ request, events = encode (completed events) ++ [.recv request] ∧
            finish = .pending current request) := by
  constructor
  · intro exec
    obtain ⟨trace, current, valid, ready | pending⟩ := exec_iff.mp exec
    · obtain ⟨rfl, rfl⟩ := ready
      rw [completed_encode]
      exact ⟨current, valid, .inl ⟨rfl, rfl⟩⟩
    · obtain ⟨request, rfl, rfl⟩ := pending
      have projected : completed (encode trace ++ [.recv request]) = trace := by
        unfold completed
        rw [List.filterMap_append]
        change completed (encode trace) ++ [] = trace
        rw [completed_encode, List.append_nil]
      rw [projected]
      exact ⟨current, valid, .inr ⟨request, rfl, rfl⟩⟩
  · rintro ⟨current, valid, shape⟩
    exact exec_iff.mpr ⟨completed events, current, valid, shape⟩

theorem completed_blocked_iff {State : Type} {handler : Handler State} {start : State}
    {events : List Event} :
    (runtime handler).beh start (.blocked events) ↔
      events = encode (completed events) ∧ ∃ final, Trace.Valid handler start (completed events) final := by
  constructor
  · intro observed
    obtain ⟨trace, final, valid, rfl⟩ := blocked_iff.mp observed
    rw [completed_encode]
    exact ⟨rfl, final, valid⟩
  · rintro ⟨shape, final, valid⟩
    exact blocked_iff.mpr ⟨completed events, final, valid, shape⟩

theorem blocked_retaining_page (capacity : Nat) (start : FileState) (page : Page) (events : List Event)
    (observed : (runtime (readWrite capacity)).beh start (.blocked events))
    (allowed : ∀ exchange ∈ completed events, RetainsPage page exchange)
    (complete : page.offset + page.size ≤ start.bytes.length) (positive : 0 < page.size) :
    events = encode (completed events) ∧
      ∃ final, Trace.Valid (readWrite capacity) start (completed events) final ∧
        CacheHit.AgreesOnPage start final page ∧ final.mode page.handle = start.mode page.handle := by
  obtain ⟨eventShape, final, valid⟩ := completed_blocked_iff.mp observed
  exact ⟨eventShape, final, valid, trace_retains_page page valid allowed complete positive⟩

end Silmaril.Proofs.Containers.SqliteVfs.Completed
