module

import Silmaril.Process.Memory.Trace.Thms
import Silmaril.Semantics.ReadWrite.Labelled.Thms

namespace Silmaril.Process.Memory

open Silmaril.Semantics.ReadWrite

private def initial : Memory :=
  ⟨[⟨16, 2, ⟨true, true, false⟩⟩], install ∅ 16 [0x11, 0x22]⟩

private def final : Memory := { initial with bytes := install initial.bytes 16 [0x42] }

private def writeRead : Trace Nat Byte := [.write 16 0x42, .read 16 0x42]
private def readUntouched : Trace Nat Byte := [.write 16 0x42, .read 17 0x22]

private theorem wrote : byteAccess.write initial 16 0x42 = some final := rfl

private theorem read_byte {memory : Memory} {address : Nat} {value : Byte}
    (allowed : memory.checkSpan .read address 1 = true)
    (backed : memory.bytes.get? address = some value) :
    byteAccess.read memory address = some value := by
  unfold byteAccess readBytes readWith
  simp only [allowed, ite_true, readBacking, backed]
  rfl

private theorem read_written : byteAccess.read final 16 = some 0x42 := by
  apply read_byte rfl
  simpa [final] using install_get initial.bytes 16 [0x42] 0 (by decide)

example : writeRead.run byteAccess initial = some final :=
  Trace.run_eq_some_iff.mpr ⟨final, wrote, read_written, rfl⟩

example : Trace.run byteAccess [.write 16 0x42, .read 16 0x11] initial = none := by
  apply Trace.run_eq_none_iff.mpr
  rintro ⟨_, next, written, observed, _⟩
  rw [wrote] at written
  cases Option.some.inj written
  rw [read_written] at observed
  exact (by decide : (0x42 : Byte) ≠ 0x11) (Option.some.inj observed)

example : Trace.run byteAccess [.read 18 0x22] initial = none := rfl

private theorem untouchedReplay : readUntouched.Replays byteAccess initial final := by
  have untouched : byteAccess.read initial 17 = some 0x22 := by
    apply read_byte rfl
    simpa [initial] using install_get (∅ : ByteMemory) 16 [0x11, 0x22] 1 (by decide)
  exact ⟨final, wrote, (byteAccess_frames wrote (by decide : 17 ≠ 16)).trans untouched, rfl⟩

example : byteAccess.labelled.Path initial readUntouched final :=
  Trace.replays_iff_path.mp untouchedReplay

example : WritesWithin initial final readUntouched.Defs :=
  replay_writesWithin untouchedReplay

example : readUntouched.Footprint 17 ∧ readUntouched.Uses 17 ∧ ¬ readUntouched.Defs 17 := by
  simp [readUntouched, Trace.Footprint, Trace.Reads, Trace.Uses, Trace.Defs, Trace.reads, Trace.writes]

example : readUntouched.reads.toTrace.Replays byteAccess initial initial := by
  apply untouchedReplay.reads_of_disjoint byteAccess_frames
  intro address reads writes
  simp [readUntouched, Trace.Reads, Trace.Defs, Trace.reads, Trace.writes] at reads writes
  omega

end Silmaril.Process.Memory
