module

public import Silmaril.Process.Memory.Trace.Defs
import Silmaril.Semantics.ReadWrite.Thms

public section
namespace Silmaril.Proofs.Process.Memory

open Silmaril.Process Silmaril.Process.Memory Silmaril.Semantics

private theorem byteWrite_frame {before after : Memory} {address : Nat} {value : Byte}
    (written : byteAccess.write before address value = some after) :
    WritesWithin before after (· = address) := by
  have only : WritesOnly before after address 1 := writeBytes_writesOnly (bytes := [value]) written
  exact ((writesOnly_iff_writesWithin before after address 1).mp only).mono (by
    intro location inside
    omega)

theorem byteAccess_frames : byteAccess.Frames byteAccess.read := by
  intro before after address value other written different
  have read := (byteWrite_frame written).readBytes (address := other) (length := 1) (by
    intro offset bound
    omega)
  change (after.readBytes other 1).bind List.head? = (before.readBytes other 1).bind List.head?
  rw [read]

theorem replay_writesWithin {trace : ReadWrite.Trace Nat Byte} {before after : Memory}
    (run : trace.Replays byteAccess before after) :
    WritesWithin before after trace.Defs := by
  refine ⟨?_, fun address outside => run.frame (observe := fun m p => m.bytes.get? p) ?_ outside⟩
  · exact run.invariant (P := fun m => m.regions = before.regions) rfl
      (fun _ _ _ _ step preserved => (byteWrite_frame step).1.trans preserved)
  · intro initial next writtenAddr value other step different
    exact (byteWrite_frame step).2 other different

end Silmaril.Proofs.Process.Memory
