module

import Silmaril.Process.Memory.Trace.Projections.Thms

namespace Silmaril.Process.Memory

open Silmaril.Semantics.ReadWrite

private def initial : Memory :=
  ⟨[⟨16, 1, ⟨true, true, false⟩⟩, ⟨17, 1, ⟨true, false, false⟩⟩,
    ⟨18, 1, ⟨false, true, false⟩⟩], install ∅ 16 [0x11, 0x22]⟩

private def final : Memory := { initial with bytes := install initial.bytes 16 [0x42] }

private def mixed : Trace Nat Byte := [.read 16 0x11, .write 16 0x42, .read 16 0x42]

private theorem initiallyAt16 : byteAccess.read initial 16 = some 0x11 :=
  byteAccess_read_iff.mpr ⟨rfl, by
    simpa [initial] using install_get (∅ : ByteMemory) 16 [0x11, 0x22] 0 (by decide)⟩

private theorem initiallyAt17 : byteAccess.read initial 17 = some 0x22 :=
  byteAccess_read_iff.mpr ⟨rfl, by
    simpa [initial] using install_get (∅ : ByteMemory) 16 [0x11, 0x22] 1 (by decide)⟩

private theorem write16 : byteAccess.write initial 16 0x42 = some final := rfl

private theorem mixedReplay : mixed.Replays byteAccess initial final :=
  ⟨initiallyAt16, final, write16, byteAccess_read_iff.mpr ⟨rfl, by
    simpa [final] using install_get initial.bytes 16 [0x42] 0 (by decide)⟩, rfl⟩

example : mixed.ReadsMatchLastWrite 16 := replay_readsMatchLastWrite mixedReplay 16

example : (writeProjection mixed).run initial = some final :=
  ByteWriteTrace.run_eq_some_iff.mpr (writeProjection_replays mixedReplay)

example : final.bytes.get? 17 = initial.bytes.get? 17 :=
  (writeProjection_replays mixedReplay).writesWithin.2 17 (by
    simp [writeProjection, mixed, Trace.writes, List.filterMap])

-- Erasing the write preserves the observations as data, but rejects the changed read.
example : (readProjection mixed).run initial = none := by
  apply Trace.run_eq_none_iff.mpr
  rintro ⟨after, replay⟩
  have agrees := (ReadTrace.replays_iff mixed.reads).mp replay
  have read := agrees.2 (16, 0x42) (List.mem_cons_of_mem _ List.mem_cons_self)
  rw [initiallyAt16] at read
  exact (by decide : (0x11 : Byte) ≠ 0x42) (Option.some.inj read)

-- Repeated reads of a read-only byte leave the entire memory unchanged.
private def reads : ByteReadTrace := ⟨[(17, 0x22), (17, 0x22)]⟩

example : reads.run initial = some initial :=
  ByteReadTrace.run_eq_some_iff.mpr ⟨initiallyAt17, initiallyAt17, rfl⟩

example : (ByteWriteTrace.mk [(17, 0x42)]).run initial = none := rfl

-- Writing a mapped, write-only byte initializes backing but does not grant read permission.
private def writes : ByteWriteTrace := ⟨[(18, 0x11), (18, 0x42)]⟩
private def middle : Memory := { initial with bytes := install initial.bytes 18 [0x11] }
private def initialized : Memory := { middle with bytes := install middle.bytes 18 [0x42] }

example : writes.run initial = some initialized :=
  ByteWriteTrace.run_eq_some_iff.mpr ⟨middle, rfl, initialized, rfl, rfl⟩

example : initialized.bytes.get? 18 = some 0x42 := by
  simpa [initialized] using install_get middle.bytes 18 [0x42] 0 (by decide)

example : (ByteReadTrace.mk [(18, 0x42)]).run initialized = none := rfl
example : (ByteReadTrace.mk [(19, 0x42)]).run initial = none := rfl

end Silmaril.Process.Memory
