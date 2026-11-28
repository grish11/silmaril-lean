module

public import Silmaril.Process.Memory.Trace.Projections.Defs
import Silmaril.Process.Memory.Trace.Thms
public import Silmaril.Semantics.ReadWrite.Observations.Defs

public section
namespace Silmaril.Proofs.Process.Memory.Projections

open Silmaril.Process Silmaril.Process.Memory Silmaril.Semantics.ReadWrite

theorem byteAccess_read_iff {memory : Memory} {address : Nat} {value : Byte} :
    byteAccess.read memory address = some value ↔
      memory.Permitted .read address 1 ∧ memory.bytes.get? address = some value := by
  change (memory.readBytes address 1).bind List.head? = some value ↔ _
  unfold Memory.readBytes Memory.readWith Memory.Permitted
  rw [Std.ExtHashMap.get?_eq_getElem?]
  by_cases permitted : memory.checkSpan .read address 1 = true
  · cases backed : memory.bytes[address]? <;> simp [permitted, Memory.readBacking, backed]
  · simp [permitted]

theorem byteAccess_readsAfterWrite : byteAccess.ReadsAfterWrite := by
  intro before after address written observed write read
  have installed := writeBytes_get (bytes := [written]) write 0 (by simp)
  exact Option.some.inj ((byteAccess_read_iff.mp read).2.symm.trans (by simpa using installed))

theorem read_replays_iff {reads : ByteReadTrace} {before after : Memory} :
    reads.Replays before after ↔ before = after ∧
      ∀ entry ∈ reads.observations,
        before.Permitted .read entry.1 1 ∧ before.bytes.get? entry.1 = some entry.2 := by
  change reads.observations.toTrace.Replays byteAccess before after ↔ _
  rw [ReadTrace.replays_iff]
  simp only [ReadTrace.Agrees, byteAccess_read_iff]

theorem write_consistent_iff {writes : ByteWriteTrace} {before : Memory} :
    (∃ after, writes.Replays before after) ↔
      ∀ entry ∈ writes.assignments, before.Permitted .write entry.1 1 := by
  obtain ⟨entries⟩ := writes
  induction entries generalizing before with
  | nil => simp [ByteWriteTrace.Replays, ByteWriteTrace.toTrace, WriteTrace.toTrace, Trace.Replays]
  | cons entry rest ih =>
    obtain ⟨address, value⟩ := entry
    change (∃ after next, byteAccess.write before address value = some next ∧
        (⟨rest⟩ : ByteWriteTrace).Replays next after) ↔
      ∀ entry ∈ (address, value) :: rest, before.Permitted .write entry.1 1
    constructor
    · rintro ⟨after, next, write, tail⟩ entry member
      have frame := writeBytes_writesOnly (bytes := [value]) write
      have stable := (writesOnly_iff_writesWithin before next address 1).mp frame
      rcases List.mem_cons.mp member with rfl | memTail
      · exact writeBytes_permitted (bytes := [value]) write
      · exact (stable.permitted_iff .write entry.1 1).mp (ih.mp ⟨after, tail⟩ entry memTail)
    · intro allPermitted
      have allowed := allPermitted (address, value) List.mem_cons_self
      let next := { before with bytes := install before.bytes address [value] }
      have write : byteAccess.write before address value = some next := by
        change before.writeBytes address [value] = some next
        simp only [writeBytes, show before.checkSpan .write address [value].length = true from allowed,
          ite_true, next]
      have frame := writeBytes_writesOnly (bytes := [value]) write
      have stable := (writesOnly_iff_writesWithin before next address 1).mp frame
      obtain ⟨after, tail⟩ := ih.mpr (fun entry member =>
        (stable.permitted_iff .write entry.1 1).mpr (allPermitted entry (List.mem_cons_of_mem _ member)))
      exact ⟨after, next, write, tail⟩

theorem write_replays_writesWithin {writes : ByteWriteTrace} {before after : Memory}
    (replay : writes.Replays before after) :
    WritesWithin before after (fun address => ∃ value, (address, value) ∈ writes.assignments) := by
  exact (replay_writesWithin replay).mono (fun _ assigned => by
    simpa only [Trace.Defs, ByteWriteTrace.toTrace, WriteTrace.writes_toTrace] using assigned)

end Silmaril.Proofs.Process.Memory.Projections
