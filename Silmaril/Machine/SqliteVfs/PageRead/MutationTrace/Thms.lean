module

public import Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.CacheHit.Defs
import Silmaril.Proofs.Machine.SqliteVfs.PageRead.MutationTrace.Compose

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.MutationTrace

open CacheHit (AgreesOnPage runHit? runPage?)
open Silmaril.Formats.Sqlite

/-- A valid finite sequence of retaining mutations preserves the observed
page bytes and handle mode from the initial to the final file state. -/
theorem trace_retains_page {capacity : Nat} {before after : FileState} {trace : Trace} (page : Page)
    (valid : Trace.Valid (readWrite capacity) before trace after)
    (allowed : ∀ exchange ∈ trace, RetainsPage page exchange)
    (complete : page.offset + page.size ≤ before.bytes.length) (positive : 0 < page.size) :
    AgreesOnPage before after page ∧ after.mode page.handle = before.mode page.handle :=
  Proofs.Machine.SqliteVfs.PageRead.MutationTrace.trace_retains_page page valid allowed complete positive

/-- The original fill, retaining mutations, and reference refetch form a valid
trace of the same read-write backing. Using the cached bytes gives the same
complete optional VDBE outcome as using the refetched bytes. -/
theorem runHit_after_mutation_trace (capacity : Nat) (before after : FileState) (trace : Trace)
    (cache : Cache) (target : SlotId) (page : Page) (owned : cache target = some .vacant)
    (admitted : page.Admitted) (live : (before.mode page.handle).isNone = false)
    (complete : page.offset + page.size ≤ before.bytes.length)
    (valid : Trace.Valid (readWrite capacity) before trace after)
    (allowed : ∀ exchange ∈ trace, RetainsPage page exchange) :
    let original := fill (readWrite capacity) before cache target page
    let fresh := fill (readWrite capacity) after cache target page
    Trace.Valid (readWrite capacity) before (original.trace ++ trace ++ fresh.trace) after ∧
      ∀ (base db root : Nat) (program : Vdbe.Program) (fuel : Nat) (initial : Vdbe.State),
        runHit? original.cache target page base db root program fuel initial =
          runPage? fresh.result.toOption base db root program fuel initial :=
  Proofs.Machine.SqliteVfs.PageRead.MutationTrace.runHit_after_mutation_trace capacity before after
    trace cache target page owned admitted live complete valid allowed

end Silmaril.Machine.SqliteVfs.PageRead.MutationTrace
