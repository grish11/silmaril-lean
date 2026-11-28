module

public import Silmaril.Process.Memory.Trace.Projections.Defs
public import Silmaril.Process.Memory.Trace.Thms
public import Silmaril.Semantics.ReadWrite.Observations.Thms
import Silmaril.Proofs.Process.Memory.Trace.Projections.Laws

public section
namespace Silmaril.Process.Memory

open Silmaril.Semantics.ReadWrite

variable {before after : Memory} {trace : Trace Nat Byte}
variable {reads : ByteReadTrace} {writes : ByteWriteTrace}

theorem byteAccess_read_iff {memory : Memory} {address : Nat} {value : Byte} :
    byteAccess.read memory address = some value ↔
      memory.Permitted .read address 1 ∧ memory.bytes.get? address = some value :=
  Proofs.Process.Memory.Projections.byteAccess_read_iff

theorem byteAccess_readsAfterWrite : byteAccess.ReadsAfterWrite :=
  Proofs.Process.Memory.Projections.byteAccess_readsAfterWrite

@[simp] theorem readProjection_toTrace : readProjection reads.toTrace = reads :=
  congrArg ByteReadTrace.mk (ReadTrace.reads_toTrace reads.observations)

@[simp] theorem writeProjection_toTrace : writeProjection writes.toTrace = writes :=
  congrArg ByteWriteTrace.mk (WriteTrace.writes_toTrace writes.assignments)

theorem ByteReadTrace.run_eq_some_iff : reads.run before = some after ↔ reads.Replays before after :=
  Trace.run_eq_some_iff

/-- Successful read-only replay preserves the entire memory. Every observation
requires read permission and the expected backing byte in that memory. -/
theorem ByteReadTrace.replays_iff :
    reads.Replays before after ↔ before = after ∧
      ∀ entry ∈ reads.observations,
        before.Permitted .read entry.1 1 ∧ before.bytes.get? entry.1 = some entry.2 :=
  Proofs.Process.Memory.Projections.read_replays_iff

theorem ByteWriteTrace.run_eq_some_iff :
    writes.run before = some after ↔ writes.Replays before after :=
  Trace.run_eq_some_iff

/-- Write-only replay succeeds exactly when the initial mapping permits every
assignment. Byte writes preserve that mapping and can initialize backing. -/
theorem ByteWriteTrace.consistent_iff :
    (∃ after, writes.Replays before after) ↔
      ∀ entry ∈ writes.assignments, before.Permitted .write entry.1 1 :=
  Proofs.Process.Memory.Projections.write_consistent_iff

/-- Unassigned backing bytes and all mapping permissions are preserved. -/
theorem ByteWriteTrace.Replays.writesWithin (replay : writes.Replays before after) :
    WritesWithin before after (fun address => ∃ value, (address, value) ∈ writes.assignments) :=
  Proofs.Process.Memory.Projections.write_replays_writesWithin replay

theorem writeProjection_replays (replay : trace.Replays byteAccess before after) :
    (writeProjection trace).Replays before after :=
  replay.writes

theorem readProjection_replays_of_disjoint (replay : trace.Replays byteAccess before after)
    (disjoint : ∀ address, trace.Reads address → ¬ trace.Defs address) :
    (readProjection trace).Replays before before :=
  replay.reads_of_disjoint byteAccess_frames disjoint

theorem replay_readsMatchLastWrite (replay : trace.Replays byteAccess before after) (address : Nat) :
    trace.ReadsMatchLastWrite address :=
  replay.matchLastWrite byteAccess_frames byteAccess_readsAfterWrite

end Silmaril.Process.Memory
